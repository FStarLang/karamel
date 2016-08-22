(** This module rewrites the original AST to send it into Low*, the subset we
 * know how to translate to C. *)

open Ast
open DeBruijn
open Idents
open Error

let ptyp = PrintAst.ptyp
let pexpr = PrintAst.pexpr

(* Some helpers ***************************************************************)

type ('a, 'b, 'c, 'd, 'e) visitor = ('a, 'b, 'c, 'd) #Ast.visitor as 'e

let visit_program (env: 'env) (visitor: _ visitor) (program: program) =
  List.map (visitor#visit_d env) program

let visit_file (env: 'env) (visitor: _ visitor) (file: file) =
  let name, program = file in
  name, visit_program env visitor program

let visit_files (env: 'env) (visitor: _ visitor) (files: file list) =
  KList.filter_map (fun f ->
    try
      Some (visit_file env visitor f)
    with Error e ->
      Printf.eprintf "Warning: dropping %s [in simplify]: %s\n" (fst f) e;
      None
  ) files


class ignore_everything = object
  method dfunction () ret name binders expr =
    DFunction (ret, name, binders, expr)

  method dglobal () name typ expr =
    DGlobal (name, typ, expr)

  method dtypealias () name t =
    DTypeAlias (name, t)

  method dtypeflat () name fields =
    DTypeFlat (name, fields)
end


(* Count the number of occurrences of each variable ***************************)

let count_use = object (self)

  inherit [binder list] map

  method! extend env binder =
    binder :: env

  method! ebound env i =
    let b = List.nth env i in
    incr b.mark;
    EBound i

  method! elet env b e1 e2 =
    (* Remove unused variables. Important to get rid of calls to [HST.get()]. *)
    let e1 = self#visit env e1 in
    let env = self#extend env b in
    let e2 = self#visit env e2 in
    match e1, !(b.mark) with
    | EConstant _, 0 ->
        snd (open_binder b e2)
    | _ ->
        ELet (b, e1, e2)

end

(* F* extraction generates these degenerate cases *****************************)

let dummy_match = object (self)

  inherit [unit] map

  method! ematch () e branches t =
    match e, branches with
    | EUnit, [ PUnit, body ] ->
        self # visit () body
    | _, [ PBool true, b1; PVar v, b2 ] when !(v.mark) = 0 ->
        let b1 = self # visit () b1 in
        let _, b2 = open_binder v b2 in
        let b2 = self # visit () b2 in
        EIfThenElse (e, b1, b2, t)
    | _ ->
        EMatch (e, self # branches () branches, t)

end


(* Get wraparound semantics for arithmetic operations using casts to uint_* ***)

let wrapping_arithmetic = object (self)

  inherit [unit] map

  method! eapp () e es =
    match e, es with
    | EOp (((K.AddW | K.SubW) as op), w), [ e1; e2 ] when K.is_signed w ->
        let e = EOp (K.without_wrap op, K.unsigned_of_signed w) in
        let e1 = self # visit () e1 in
        let e2 = self # visit () e2 in
        ECast (EApp (e, [ ECast (e1, TInt (K.unsigned_of_signed w)); e2 ]), TInt w)

    | EOp (((K.AddW | K.SubW) as op), w), [ e1; e2 ] when K.is_unsigned w ->
        let e = EOp (K.without_wrap op, w) in
        let e1 = self # visit () e1 in
        let e2 = self # visit () e2 in
        EApp (e, [ e1; e2 ])

    | e, es ->
        EApp (self # visit () e, List.map (self # visit ()) es)
end


(* Convert back and forth between [e1; e2] and [let _ = e1 in e2]. *)

let sequence_binding () = {
  name = "_";
  typ = TUnit;
  mut = false;
  mark = ref 0;
  meta = Some MetaSequence;
  atom = Atom.fresh ()
}

let sequence_to_let = object (self)

  inherit [unit] map

  method! esequence () es =
    let es = List.map (self#visit ()) es in
    match List.rev es with
    | last :: first_fews ->
        List.fold_left (fun cont e ->
          ELet (sequence_binding (), e, lift 1 cont)
        ) last first_fews
    | [] ->
        failwith "[sequence_to_let]: impossible (empty sequence)"

end

let let_to_sequence = object (self)

  inherit [unit] map

  method! elet env b e1 e2 =
    match b.meta with
    | Some MetaSequence ->
        let e1 = self#visit env e1 in
        let b, e2 = open_binder b e2 in
        let e2 = self#visit env e2 in
        assert (b.typ = TUnit && b.name = "_");
        begin match e1, e2 with
        | _, EUnit ->
            (* let _ = e1 in () *)
            e1
        | ECast (EUnit, _), _
        | EUnit, _ ->
            (* let _ = () in e2 *)
            e2
        | _, ESequence es ->
            ESequence (e1 :: es)
        | _ ->
            ESequence [e1; e2]
        end
    | None ->
        let e2 = self#visit env e2 in
        ELet (b, e1, e2)

end

let rec nest_in_lets f = function
  | ELet (b, e1, e2) ->
      ELet (b, e1, nest_in_lets f e2)
  | e ->
      f e

let let_if_to_assign = object (self)

  inherit [unit] map

  method! elet () b e1 e2 =
    match e1, b.meta with
    | EIfThenElse (cond, e_then, e_else, _), None ->
        let b = { b with mut = true } in
        let b, e2 = open_binder b e2 in
        let nest_assign = nest_in_lets (fun innermost -> EAssign (EOpen (b.name, b.atom), innermost)) in
        let e_then = nest_assign e_then in
        let e_else = nest_assign e_else in
        ELet (b, EAny,
          close_binder b (lift 1 (ELet (sequence_binding (), EIfThenElse (cond, e_then, e_else, TUnit),
            lift 1 (self#visit () e2)))))
    | _ ->
        (* There are no more nested lets at this stage *)
        ELet (b, e1, self#visit () e2)

end

(* No left-nested let-bindings ************************************************)

let nest (lhs: (binder * expr) list) (e2: expr) =
  List.fold_right (fun (binder, e1) e2 ->
    let e2 = close_binder binder e2 in
    ELet (binder, e1, e2)
  ) lhs e2

(* In a toplevel context, let-bindings may appear. A toplevel context
 * is defined inductively as:
 * - a node that stands for a function body;
 * - the continuation of an [ELet] node in a toplevel context;
 * - an element of an [ESequence] that is already in a toplevel context.
 * As soon as we leave a toplevel context, we jump into [hoist]. *)
let rec hoist_t e =
  match e with
  | EAbort
  | EAny
  | EBound _
  | EOpen _
  | EQualified _
  | EConstant _
  | EUnit
  | EPushFrame | EPopFrame
  | EBool _
  | EOp _ ->
      e

  | EApp (e, es) ->
      let lhs, e = hoist e in
      let lhss, es = List.split (List.map hoist es) in
      let lhs = lhs @ List.flatten lhss in
      nest lhs (EApp (e, es))

  | ELet (binder, EIfThenElse (e'1, e'2, e'3, t), e2) ->
      (* Will be translated into an assignment later on *)
      let lhs, e'1 = hoist e'1 in
      let e'2 = hoist_t e'2 in
      let e'3 = hoist_t e'3 in
      let binder, e2 = open_binder binder e2 in
      let e2 = hoist_t e2 in
      nest lhs (ELet (binder, EIfThenElse (e'1, e'2, e'3, t), close_binder binder e2))

  | ELet (binder, e1, e2) ->
      (* At top-level, bindings may nest on the right-hand side of let-bindings,
       * but not on the left-hand side. *)
      let lhs, e1 = hoist e1 in
      let binder, e2 = open_binder binder e2 in
      let e2 = hoist_t e2 in
      nest lhs (ELet (binder, e1, close_binder binder e2))

  | EIfThenElse (e1, e2, e3, t) ->
      let lhs, e1 = hoist e1 in
      let e2 = hoist_t e2 in
      let e3 = hoist_t e3 in
      nest lhs (EIfThenElse (e1, e2, e3, t))

  | EWhile (e1, e2) ->
      let lhs, e1 = hoist e1 in
      let e2 = hoist_t e2 in
      nest lhs (EWhile (e1, e2))

  | ESequence _ ->
      failwith "[hoist_t]: sequences should've been translated as let _ ="

  | EAssign (e1, e2) ->
      let lhs1, e1 = hoist e1 in
      let lhs2, e2 = hoist e2 in
      nest (lhs1 @ lhs2) (EAssign (e1, e2))

  | EBufCreate (e1, e2) ->
      let lhs1, e1 = hoist e1 in
      let lhs2, e2 = hoist e2 in
      nest (lhs1 @ lhs2) (EBufCreate (e1, e2))

  | EBufCreateL es ->
      let lhs, es = List.split (List.map hoist es) in
      nest (List.flatten lhs) (EBufCreateL es)

  | EBufRead (e1, e2) ->
      let lhs1, e1 = hoist e1 in
      let lhs2, e2 = hoist e2 in
      nest (lhs1 @ lhs2) (EBufRead (e1, e2))

  | EBufWrite (e1, e2, e3) ->
      let lhs1, e1 = hoist e1 in
      let lhs2, e2 = hoist e2 in
      let lhs3, e3 = hoist e3 in
      nest (lhs1 @ lhs2 @ lhs3) (EBufWrite (e1, e2, e3))

  | EBufBlit (e1, e2, e3, e4, e5) ->
      let lhs1, e1 = hoist e1 in
      let lhs2, e2 = hoist e2 in
      let lhs3, e3 = hoist e3 in
      let lhs4, e4 = hoist e4 in
      let lhs5, e5 = hoist e5 in
      nest (lhs1 @ lhs2 @ lhs3 @ lhs4 @ lhs5) (EBufBlit (e1, e2, e3, e4, e5))

  | EBufSub (e1, e2) ->
      let lhs1, e1 = hoist e1 in
      let lhs2, e2 = hoist e2 in
      nest (lhs1 @ lhs2) (EBufSub (e1, e2))

  | ECast (e, t) ->
      let lhs, e = hoist e in
      nest lhs (ECast (e, t))

  | EMatch _ ->
      failwith "[hoist_t]: EMatch not properly desugared"

  | EReturn e ->
      let lhs, e = hoist e in
      nest lhs (EReturn e)

  | EField (t, e, f) ->
      let lhs, e = hoist e in
      nest lhs (EField (t, e, f))

  | EFlat (t, fields) ->
      let lhs, fields = List.split (List.map (fun (ident, expr) ->
        let lhs, expr = hoist expr in
        lhs, (ident, expr)
      ) fields) in
      nest (List.flatten lhs) (EFlat (t, fields))

(* This traversal guarantees that no let-bindings are left in the visited term.
 * It returns a [(binder * expr) list] of all the hoisted bindings. It is up to
 * the caller to rewrite the bindings somehow and call [close_binder] on the
 * [binder]s. The bindings are ordered in the evaluation order (i.e. the first
 * binding returned should be evaluated first). *)
and hoist e =
  match e with
  | EAbort
  | EAny
  | EBound _
  | EOpen _
  | EQualified _
  | EConstant _
  | EUnit
  | EPushFrame | EPopFrame
  | EBool _
  | EOp _ ->
      [], e

  | EApp (e, es) ->
      (* TODO: assert that in the case of a lazily evaluated boolean operator,
       * there are no intermediary let-bindings there... or does F* guarantee
       * that no effectful computations can occur there? *)
      let lhs, e = hoist e in
      let lhss, es = List.split (List.map hoist es) in
      (* TODO: reverse the order and use [rev_append] here *)
      let lhs = lhs @ List.flatten lhss in
      lhs, EApp (e, es)

  | ELet (binder, e1, e2) ->
      let lhs1, e1 = hoist e1 in
      let binder, e2 = open_binder binder e2 in
      (* The caller (e.g. [hoist_t]) takes care, via [nest], of closing this
       * binder. *)
      let lhs2, e2 = hoist e2 in
      lhs1 @ [ binder, e1 ] @ lhs2, e2

  | EIfThenElse (e1, e2, e3, t) ->
      let lhs1, e1 = hoist e1 in
      let e2 = hoist_t e2 in
      let e3 = hoist_t e3 in
      let b = { name = "ite"; typ = t; mut = false; mark = ref 0; meta = None; atom = Atom.fresh () } in
      lhs1 @ [ b, EIfThenElse (e1, e2, e3, t) ], EOpen (b.name, b.atom)

  | EWhile _ ->
      throw_error "No [EWhile] in expression position"

  | ESequence _ ->
      failwith "[hoist_t]: sequences should've been translated as let _ ="

  | EAssign (e1, e2) ->
      let lhs1, e1 = hoist e1 in
      let lhs2, e2 = hoist e2 in
      lhs1 @ lhs2, EAssign (e1, e2)

  | EBufCreate (e1, e2) ->
      let lhs1, e1 = hoist e1 in
      let lhs2, e2 = hoist e2 in
      lhs1 @ lhs2, EBufCreate (e1, e2)

  | EBufCreateL es ->
      let lhs, es = List.split (List.map hoist es) in
      List.flatten lhs, EBufCreateL es

  | EBufRead (e1, e2) ->
      let lhs1, e1 = hoist e1 in
      let lhs2, e2 = hoist e2 in
      lhs1 @ lhs2, EBufRead (e1, e2)

  | EBufWrite (e1, e2, e3) ->
      let lhs1, e1 = hoist e1 in
      let lhs2, e2 = hoist e2 in
      let lhs3, e3 = hoist e3 in
      lhs1 @ lhs2 @ lhs3, EBufWrite (e1, e2, e3)

  | EBufBlit (e1, e2, e3, e4, e5) ->
      let lhs1, e1 = hoist e1 in
      let lhs2, e2 = hoist e2 in
      let lhs3, e3 = hoist e3 in
      let lhs4, e4 = hoist e4 in
      let lhs5, e5 = hoist e5 in
      lhs1 @ lhs2 @ lhs3 @ lhs4 @ lhs5, EBufBlit (e1, e2, e3, e4, e5)

  | EBufSub (e1, e2) ->
      let lhs1, e1 = hoist e1 in
      let lhs2, e2 = hoist e2 in
      lhs1 @ lhs2, EBufSub (e1, e2)

  | ECast (e, t) ->
      let lhs, e = hoist e in
      lhs, ECast (e, t)

  | EMatch _ ->
      failwith "[hoist_t]: EMatch"

  | EReturn _ ->
      throw_error "[return] expressions should only appear in statement position"

  | EField (t, e, f) ->
      let lhs, e = hoist e in
      lhs, EField (t, e, f)

  | EFlat (t, fields) ->
      let lhs, fields = List.split (List.map (fun (ident, expr) ->
        let lhs, expr = hoist expr in
        lhs, (ident, expr)
      ) fields) in
      List.flatten lhs, EFlat (t, fields)



(* No partial applications ****************************************************)

let eta_expand = object
  inherit [_] map
  inherit ignore_everything

  method dglobal () name t body =
    (* TODO: eta-expand partially applied functions *)
    match t with
    | TArrow _ ->
        let tret, targs = flatten_arrow t in
        let n = List.length targs in
        let binders, args = List.split (List.mapi (fun i t ->
          { name = Printf.sprintf "x%d" i; typ = t; mut = false; mark = ref 0; meta = None; atom = Atom.fresh () },
          EBound (n - i - 1)
        ) targs) in
        let body = EApp (body, args) in
        DFunction (tret, name, binders, body)
    | _ ->
        DGlobal (name, t, body)
end


(* Make top-level names C-compatible using a global translation table **********)

let record_name lident =
  let desired_name = if !Options.no_prefix then snd lident else string_of_lident lident in
  [], GlobalNames.record (string_of_lident lident) desired_name

let record_toplevel_names = object

  inherit [_] map

  method dglobal () name t body =
    DGlobal (record_name name, t, body)

  method dfunction () ret name args body =
    DFunction (ret, record_name name, args, body)

  method dtypealias () name t =
    DTypeAlias (record_name name, t)

  method dtypeflat () name fields =
    DTypeFlat (record_name name, fields)
end

let t lident =
  [], GlobalNames.translate (string_of_lident lident)

let replace_references_to_toplevel_names = object(self)
  inherit [unit] map

  method tqualified () lident =
    TQualified (t lident)

  method equalified () lident =
    EQualified (t lident)

  method eflat () lident fields =
    EFlat (t lident, self#fields () fields)

  method efield () lident e field =
    EField (t lident, self#visit () e, field)
end


(* Everything composed together ***********************************************)

let simplify (files: file list): file list =
  let files = visit_files () record_toplevel_names files in
  let files = visit_files () replace_references_to_toplevel_names files in
  let files = visit_files () eta_expand files in
  let files = visit_files [] count_use files in
  let files = visit_files () dummy_match files in
  let files = visit_files () wrapping_arithmetic files in
  let files = visit_files () sequence_to_let files in
  let files = visit_files () (object
    inherit ignore_everything
    inherit [_] map

    method dfunction () ret name binders expr =
      (* TODO: no nested let-bindings in top-level value declarations either *)
      let binders, expr = open_function_binders binders expr in
      let expr = hoist_t expr in
      let expr = close_function_binders binders expr in
      DFunction (ret, name, binders, expr)
  end) files in
  let files = visit_files () let_if_to_assign files in
  let files = visit_files () let_to_sequence files in
  files

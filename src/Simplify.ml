(** This module rewrites the original AST to send it into Low*, the subset we
 * know how to translate to C. *)

open Ast
open DeBruijn
open Idents
open Warnings

let ptyp = PrintAst.ptyp
let pexpr = PrintAst.pexpr

(* Some helpers ***************************************************************)

type ('a, 'b, 'c, 'd, 'e, 'f) visitor = ('a, 'b, 'c, 'd, 'e) #Ast.visitor as 'f

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
      maybe_fatal_error (fst f ^ "/" ^ fst e, snd e);
      None
  ) files


class ignore_everything = object
  method dfunction () ret name binders expr =
    DFunction (ret, name, binders, expr)

  method dglobal () name typ expr =
    DGlobal (name, typ, expr)

  method dtypealias () name n t =
    DTypeAlias (name, n, t)

  method dtypeflat () name fields =
    DTypeFlat (name, fields)
end


(* Count the number of occurrences of each variable ***************************)

let rec is_pure { node; _ } =
  match node with
  | EConstant _ -> true
  | ECast (e, _) -> is_pure e
  | _ -> false

let count_use = object (self)

  inherit [binder list] map

  method! extend env binder =
    binder :: env

  method! ebound env _ i =
    let b = List.nth env i in
    incr b.mark;
    EBound i

  method! elet env _ b e1 e2 =
    (* Remove unused variables. Important to get rid of calls to [HST.get()]. *)
    let e1 = self#visit env e1 in
    let env = self#extend env b in
    let e2 = self#visit env e2 in
    match e1, !(b.mark) with
    | e, 0 when is_pure e ->
        (snd (open_binder b e2)).node
    | _ ->
        ELet (b, e1, e2)

end

(* F* extraction generates these degenerate cases *****************************)

let dummy_match = object (self)

  inherit [unit] map

  method! ematch () _ e branches =
    match e.node, branches with
    | EUnit, [ PUnit, body ] ->
        (self#visit () body).node
    | _, [ PBool true, b1; PVar v, b2 ] when !(v.mark) = 0 ->
        let b1 = self#visit () b1 in
        let _, b2 = open_binder v b2 in
        let b2 = self#visit () b2 in
        EIfThenElse (e, b1, b2)
    | _ ->
        EMatch (e, self#branches () branches)

end


(* Get wraparound semantics for arithmetic operations using casts to uint_* ***)

let wrapping_arithmetic = object (self)

  inherit [unit] map

  method! eapp () _ e es =
    match e.node, es with
    | EOp (((K.AddW | K.SubW) as op), w), [ e1; e2 ] when K.is_signed w ->
        let unsigned_w = K.unsigned_of_signed w in
        let e = {
          node = EOp (K.without_wrap op, unsigned_w);
          mtyp = Checker.type_of_op (K.without_wrap op) unsigned_w
        } in
        let e1 = self#visit () e1 in
        let e2 = self#visit () e2 in
        let c e = { node = ECast (e, TInt unsigned_w); mtyp = TInt unsigned_w } in
        (** TODO: the second call to [c] is optional per the C semantics, but in
         * order to preserve typing, we have to insert it... maybe recognize
         * that pattern later on at the C emission level? *)
        let unsigned_app = { node = EApp (e, [ c e1; c e2 ]); mtyp = TInt unsigned_w } in
        ECast (unsigned_app, TInt w)

    | EOp (((K.AddW | K.SubW) as op), w), [ e1; e2 ] when K.is_unsigned w ->
        let e = {
          node = EOp (K.without_wrap op, w);
          mtyp = Checker.type_of_op (K.without_wrap op) w
        }  in
        let e1 = self#visit () e1 in
        let e2 = self#visit () e2 in
        EApp (e, [ e1; e2 ])

    | _, es ->
        EApp (self#visit () e, List.map (self#visit ()) es)
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

  method! esequence () _ es =
    let es = List.map (self#visit ()) es in
    match List.rev es with
    | last :: first_fews ->
        (List.fold_left (fun cont e ->
          { node = ELet (sequence_binding (), e, lift 1 cont); mtyp = last.mtyp }
        ) last first_fews).node
    | [] ->
        failwith "[sequence_to_let]: impossible (empty sequence)"

end

let let_to_sequence = object (self)

  inherit [unit] map

  method! elet env _ b e1 e2 =
    match b.meta with
    | Some MetaSequence ->
        let e1 = self#visit env e1 in
        let b, e2 = open_binder b e2 in
        let e2 = self#visit env e2 in
        assert (b.typ = TUnit && b.name = "_");
        begin match e1.node, e2.node with
        | _, EUnit ->
            (* let _ = e1 in () *)
            e1.node
        | ECast ({ node = EUnit; _ }, _), _
        | EUnit, _ ->
            (* let _ = () in e2 *)
            e2.node
        | _, ESequence es ->
            ESequence (e1 :: es)
        | _ ->
            ESequence [e1; e2]
        end
    | None ->
        let e2 = self#visit env e2 in
        ELet (b, e1, e2)

end

let rec nest_in_lets f e =
  match e.node with
  | ELet (b, e1, e2) ->
      { node = ELet (b, e1, nest_in_lets f e2); mtyp = TUnit }
  | _ ->
      f e

let let_if_to_assign = object (self)

  inherit [unit] map

  method! elet () _ b e1 e2 =
    match e1.node, b.meta with
    | EIfThenElse (cond, e_then, e_else), None ->
        let b = { b with mut = true } in
        let b, e2 = open_binder b e2 in
        let nest_assign = nest_in_lets (fun innermost -> {
          node = EAssign ({ node = EOpen (b.name, b.atom); mtyp = b.typ }, innermost);
          mtyp = TUnit
        }) in
        let e_then = nest_assign e_then in
        let e_else = nest_assign e_else in
        let e_ifthenelse = {
          node = EIfThenElse (cond, e_then, e_else);
          mtyp = TUnit
        } in
        ELet (b, { node = EAny; mtyp = TAny },
          close_binder b (lift 1 ({
            node = ELet (sequence_binding (), e_ifthenelse, lift 1 (self#visit () e2));
            mtyp = e2.mtyp
          })))
    | _ ->
        (* There are no more nested lets at this stage *)
        ELet (b, e1, self#visit () e2)

end

(* No left-nested let-bindings ************************************************)

let nest (lhs: (binder * expr) list) (e2: expr) =
  List.fold_right (fun (binder, e1) e2 ->
    let e2 = close_binder binder e2 in
    { node = ELet (binder, e1, e2); mtyp = e2.mtyp }
  ) lhs e2

(** Generates "let [[name]]: [[t]] = [[e]] in [[name]]" *)
let mk_named_binding name t e =
  let b = fresh_binder name t in
  b,
  { node = e; mtyp = t },
  { node = EOpen (b.name, b.atom); mtyp = t }

(* In a toplevel context, let-bindings may appear. A toplevel context
 * is defined inductively as:
 * - a node that stands for a function body;
 * - the continuation of an [ELet] node in a toplevel context;
 * - an element of an [ESequence] that is already in a toplevel context.
 * As soon as we leave a toplevel context, we jump into [hoist]. *)
let rec hoist_t e =
  let mk node = { e with node } in
  match e.node with
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
      let lhs, e = hoist false e in
      let lhss, es = List.split (List.map (hoist false) es) in
      let lhs = lhs @ List.flatten lhss in
      nest lhs (mk (EApp (e, es)))

  | ELet (binder, e1, e2) ->
      (* At top-level, bindings may nest on the right-hand side of let-bindings,
       * but not on the left-hand side. *)
      let lhs, e1 = hoist true e1 in
      let binder, e2 = open_binder binder e2 in
      let e2 = hoist_t e2 in
      nest lhs (mk (ELet (binder, e1, close_binder binder e2)))

  | EIfThenElse (e1, e2, e3) ->
      let lhs, e1 = hoist false e1 in
      let e2 = hoist_t e2 in
      let e3 = hoist_t e3 in
      nest lhs (mk (EIfThenElse (e1, e2, e3)))

  | EWhile (e1, e2) ->
      let lhs, e1 = hoist false e1 in
      let e2 = hoist_t e2 in
      nest lhs (mk (EWhile (e1, e2)))

  | ESequence _ ->
      failwith "[hoist_t]: sequences should've been translated as let _ ="

  | EAssign (e1, e2) ->
      let lhs1, e1 = hoist false e1 in
      let lhs2, e2 = hoist false e2 in
      nest (lhs1 @ lhs2) (mk (EAssign (e1, e2)))

  | EBufCreate (e1, e2) ->
      let lhs1, e1 = hoist false e1 in
      let lhs2, e2 = hoist false e2 in
      let b, body, cont = mk_named_binding "buf" e.mtyp (EBufCreate (e1, e2)) in
      nest (lhs1 @ lhs2) (mk (ELet (b, body, close_binder b cont)))

  | EBufCreateL es ->
      let lhs, es = List.split (List.map (hoist false) es) in
      let b, body, cont = mk_named_binding "buf" e.mtyp (EBufCreateL es) in
      nest (List.flatten lhs) (mk (ELet (b, body, close_binder b cont)))

  | EBufRead (e1, e2) ->
      let lhs1, e1 = hoist false e1 in
      let lhs2, e2 = hoist false e2 in
      nest (lhs1 @ lhs2) (mk (EBufRead (e1, e2)))

  | EBufWrite (e1, e2, e3) ->
      let lhs1, e1 = hoist false e1 in
      let lhs2, e2 = hoist false e2 in
      let lhs3, e3 = hoist false e3 in
      nest (lhs1 @ lhs2 @ lhs3) (mk (EBufWrite (e1, e2, e3)))

  | EBufBlit (e1, e2, e3, e4, e5) ->
      let lhs1, e1 = hoist false e1 in
      let lhs2, e2 = hoist false e2 in
      let lhs3, e3 = hoist false e3 in
      let lhs4, e4 = hoist false e4 in
      let lhs5, e5 = hoist false e5 in
      nest (lhs1 @ lhs2 @ lhs3 @ lhs4 @ lhs5) (mk (EBufBlit (e1, e2, e3, e4, e5)))
  | EBufSub (e1, e2) ->
      let lhs1, e1 = hoist false e1 in
      let lhs2, e2 = hoist false e2 in
      nest (lhs1 @ lhs2) (mk (EBufSub (e1, e2)))

  | ECast (e, t) ->
      let lhs, e = hoist false e in
      nest lhs (mk (ECast (e, t)))

  | EMatch _ ->
      failwith "[hoist_t]: EMatch not properly desugared"

  | EReturn e ->
      let lhs, e = hoist false e in
      nest lhs (mk (EReturn e))

  | EField (e, f) ->
      let lhs, e = hoist false e in
      nest lhs (mk (EField (e, f)))

  | EFlat fields ->
      let lhs, fields = List.split (List.map (fun (ident, expr) ->
        let lhs, expr = hoist false expr in
        lhs, (ident, expr)
      ) fields) in
      nest (List.flatten lhs) (mk (EFlat fields))

(* This traversal guarantees that no let-bindings are left in the visited term.
 * It returns a [(binder * expr) list] of all the hoisted bindings. It is up to
 * the caller to rewrite the bindings somehow and call [close_binder] on the
 * [binder]s. The bindings are ordered in the evaluation order (i.e. the first
 * binding returned should be evaluated first). *)
and hoist under_let e =
  let mk node = { e with node } in
  match e.node with
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
      let lhs, e = hoist false e in
      let lhss, es = List.split (List.map (hoist false) es) in
      (* TODO: reverse the order and use [rev_append] here *)
      let lhs = lhs @ List.flatten lhss in
      lhs, mk (EApp (e, es))

  | ELet (binder, e1, e2) ->
      let lhs1, e1 = hoist true e1 in
      let binder, e2 = open_binder binder e2 in
      (* The caller (e.g. [hoist_t]) takes care, via [nest], of closing this
       * binder. *)
      let lhs2, e2 = hoist false e2 in
      lhs1 @ [ binder, e1 ] @ lhs2, e2

  | EIfThenElse (e1, e2, e3) ->
      let t = e.mtyp in
      let lhs1, e1 = hoist false e1 in
      let e2 = hoist_t e2 in
      let e3 = hoist_t e3 in
      if under_let then
        lhs1, mk (EIfThenElse (e1, e2, e3))
      else
        let b, body, cont = mk_named_binding "ite" t (EIfThenElse (e1, e2, e3)) in
        lhs1 @ [ b, body ], cont

  | EWhile (e1, e2) ->
      let lhs1, e1 = hoist false e1 in
      let e2 = hoist_t e2 in
      if under_let then
        lhs1, mk (EWhile (e1, e2))
      else
        let b = fresh_binder "_" TUnit in
        let b = { b with meta = Some MetaSequence } in
        lhs1 @ [ b, mk (EWhile (e1, e2)) ], mk EUnit

  | ESequence _ ->
      fatal_error "[hoist_t]: sequences should've been translated as let _ ="

  | EAssign (e1, e2) ->
      let lhs1, e1 = hoist false e1 in
      let lhs2, e2 = hoist false e2 in
      lhs1 @ lhs2, mk (EAssign (e1, e2))

  | EBufCreate (e1, e2) ->
      let t = e.mtyp in
      let lhs1, e1 = hoist false e1 in
      let lhs2, e2 = hoist false e2 in
      if under_let then
        lhs1 @ lhs2, mk (EBufCreate (e1, e2))
      else
        let b, body, cont = mk_named_binding "buf" t (EBufCreate (e1, e2)) in
        lhs1 @ lhs2 @ [ b, body ], cont

  | EBufCreateL es ->
      let t = e.mtyp in
      let lhs, es = List.split (List.map (hoist false) es) in
      let lhs = List.flatten lhs in
      if under_let then
        lhs, mk (EBufCreateL es)
      else
        let b, body, cont = mk_named_binding "buf" t (EBufCreateL es) in
        lhs @ [ b, body ], cont

  | EBufRead (e1, e2) ->
      let lhs1, e1 = hoist false e1 in
      let lhs2, e2 = hoist false e2 in
      lhs1 @ lhs2, mk (EBufRead (e1, e2))

  | EBufWrite (e1, e2, e3) ->
      let lhs1, e1 = hoist false e1 in
      let lhs2, e2 = hoist false e2 in
      let lhs3, e3 = hoist false e3 in
      lhs1 @ lhs2 @ lhs3, mk (EBufWrite (e1, e2, e3))

  | EBufBlit (e1, e2, e3, e4, e5) ->
      let lhs1, e1 = hoist false e1 in
      let lhs2, e2 = hoist false e2 in
      let lhs3, e3 = hoist false e3 in
      let lhs4, e4 = hoist false e4 in
      let lhs5, e5 = hoist false e5 in
      lhs1 @ lhs2 @ lhs3 @ lhs4 @ lhs5, mk (EBufBlit (e1, e2, e3, e4, e5))

  | EBufSub (e1, e2) ->
      let lhs1, e1 = hoist false e1 in
      let lhs2, e2 = hoist false e2 in
      lhs1 @ lhs2, mk (EBufSub (e1, e2))

  | ECast (e, t) ->
      let lhs, e = hoist false e in
      lhs, mk (ECast (e, t))

  | EMatch _ ->
      failwith "[hoist_t]: EMatch"

  | EReturn _ ->
      raise_error (Unsupported "[return] expressions should only appear in statement position")

  | EField (e, f) ->
      let lhs, e = hoist false e in
      lhs, mk (EField (e, f))

  | EFlat fields ->
      let lhs, fields = List.split (List.map (fun (ident, expr) ->
        let lhs, expr = hoist false expr in
        lhs, (ident, expr)
      ) fields) in
      List.flatten lhs, mk (EFlat fields)



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
          { node = EBound (n - i - 1); mtyp = t }
        ) targs) in
        let body = { node = EApp (body, args); mtyp = tret } in
        DFunction (tret, name, binders, body)
    | _ ->
        DGlobal (name, t, body)
end


(* Make top-level names C-compatible using a global translation table **********)

let record_name lident =
  let desired_name =
    if List.exists ((=) (String.concat "." (fst lident))) !Options.no_prefix then
      snd lident
    else
      string_of_lident lident
  in
  [], GlobalNames.record (string_of_lident lident) desired_name

let record_toplevel_names = object

  inherit [_] map

  method dglobal () name t body =
    DGlobal (record_name name, t, body)

  method dfunction () ret name args body =
    DFunction (ret, record_name name, args, body)

  method dexternal () name t =
    DExternal (record_name name, t)

  method dtypealias () name n t =
    DTypeAlias (record_name name, n, t)

  method dtypeflat () name fields =
    DTypeFlat (record_name name, fields)
end

let t lident =
  [], GlobalNames.translate (string_of_lident lident)

let replace_references_to_toplevel_names = object(self)
  inherit [unit] map

  method tapp () lident args =
    TApp (t lident, List.map (self#visit_t ()) args)

  method tqualified () lident =
    TQualified (t lident)

  method equalified () _ lident =
    EQualified (t lident)

  method dglobal () name typ body =
    DGlobal (t name, self#visit_t () typ, self#visit () body)

  method dfunction () ret name args body =
    DFunction (self#visit_t () ret, t name, self#binders () args, self#visit () body)

  method dtypealias () name n typ =
    DTypeAlias (t name, n, self#visit_t () typ)

  method dexternal () name typ =
    DExternal (t name, self#visit_t () typ)

  method dtypeflat () name fields =
    DTypeFlat (t name, self#fields_t () fields)

end


(* Everything composed together ***********************************************)

let simplify1 (files: file list): file list =
  let files = visit_files () record_toplevel_names files in
  let files = visit_files () replace_references_to_toplevel_names files in
  let files = visit_files () eta_expand files in
  let files = visit_files [] count_use files in
  let files = visit_files () dummy_match files in
  let files = visit_files () wrapping_arithmetic files in
  files

let simplify2 (files: file list): file list =
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

let simplify (files: file list): file list =
  let files = simplify1 files in
  let files = simplify2 files in
  files

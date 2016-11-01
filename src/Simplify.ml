(** This module rewrites the original AST to send it into Low*, the subset we
 * know how to translate to C. *)

open Ast
open DeBruijn
open Idents
open Warnings

(* Some helpers ***************************************************************)

let visit_files (env: 'env) (visitor: _ map) (files: file list) =
  KList.filter_map (fun f ->
    try
      Some (visitor#visit_file env f)
    with Error e ->
      maybe_fatal_error (fst f ^ "/" ^ fst e, snd e);
      None
  ) files


class ignore_everything = object
  method dfunction () cc flags ret name binders expr =
    DFunction (cc, flags, ret, name, binders, expr)

  method dglobal () flags name typ expr =
    DGlobal (flags, name, typ, expr)

  method dtype () name n t =
    DType (name, n, t)
end


(* Count the number of occurrences of each variable ***************************)

let rec is_pure { node; _ } =
  match node with
  | EBound _ | EOpen _
  | EConstant _ -> true
  | EField (e, _)
  | ECast (e, _) -> is_pure e
  | _ -> false

let count_use = object (self)

  inherit [binder list] map

  method! extend env binder =
    binder.node.mark := 0;
    binder :: env

  method! ebound env _ i =
    let b = List.nth env i in
    incr b.node.mark;
    EBound i

  method! elet env _ b e1 e2 =
    (* Remove unused variables. Important to get rid of calls to [HST.get()]. *)
    let e1 = self#visit env e1 in
    let env = self#extend env b in
    let e2 = self#visit env e2 in
    match e1, !(b.node.mark) with
    | e, 0 when is_pure e ->
        (snd (open_binder b e2)).node
    | _ ->
        ELet (b, e1, e2)

end


(* Get wraparound semantics for arithmetic operations using casts to uint_* ***)

let wrapping_arithmetic = object (self)

  inherit [unit] map

  method! eapp () _ e es =
    match e.node, es with
    | EOp (((K.AddW | K.SubW | K.MultW | K.DivW) as op), w), [ e1; e2 ] when K.is_signed w ->
        let unsigned_w = K.unsigned_of_signed w in
        let e = {
          node = EOp (K.without_wrap op, unsigned_w);
          typ = Checker.type_of_op (K.without_wrap op) unsigned_w
        } in
        let e1 = self#visit () e1 in
        let e2 = self#visit () e2 in
        let c e = { node = ECast (e, TInt unsigned_w); typ = TInt unsigned_w } in
        (** TODO: the second call to [c] is optional per the C semantics, but in
         * order to preserve typing, we have to insert it... maybe recognize
         * that pattern later on at the C emission level? *)
        let unsigned_app = { node = EApp (e, [ c e1; c e2 ]); typ = TInt unsigned_w } in
        ECast (unsigned_app, TInt w)

    | EOp (((K.AddW | K.SubW | K.MultW | K.DivW) as op), w), [ e1; e2 ] when K.is_unsigned w ->
        let e = {
          node = EOp (K.without_wrap op, w);
          typ = Checker.type_of_op (K.without_wrap op) w
        }  in
        let e1 = self#visit () e1 in
        let e2 = self#visit () e2 in
        EApp (e, [ e1; e2 ])

    | _, es ->
        EApp (self#visit () e, List.map (self#visit ()) es)
end


(* Convert back and forth between [e1; e2] and [let _ = e1 in e2]. *)

let sequence_binding () = with_type TUnit {
  name = "_";
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
          { node = ELet (sequence_binding (), e, lift 1 cont); typ = last.typ }
        ) last first_fews).node
    | [] ->
        failwith "[sequence_to_let]: impossible (empty sequence)"

end

let let_to_sequence = object (self)

  inherit [unit] map

  method! elet env _ b e1 e2 =
    match b.node.meta with
    | Some MetaSequence ->
        let e1 = self#visit env e1 in
        let b, e2 = open_binder b e2 in
        let e2 = self#visit env e2 in
        assert (b.typ = TUnit && b.node.name = "_");
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

let rec nest_in_return_pos f e =
  match e.node with
  | ELet (b, e1, e2) ->
      let e2 = nest_in_return_pos f e2 in
      { node = ELet (b, e1, e2); typ = TUnit }
  | EIfThenElse (e1, e2, e3) ->
      let e2 = nest_in_return_pos f e2 in
      let e3 = nest_in_return_pos f e3 in
      { node = EIfThenElse (e1, e2, e3); typ = TUnit }
  | ESwitch (e, branches) ->
      let branches = List.map (fun (t, e) ->
        t, nest_in_return_pos f e
      ) branches in
      { node = ESwitch (e, branches); typ = TUnit }
  | _ ->
      f e

let let_if_to_assign = object (self)

  inherit [unit] map

  method! elet () _ b e1 e2 =
    match e1.node, b.node.meta with
    | EIfThenElse (cond, e_then, e_else), None ->
        (* Recursively transform *)
        let e_then = self#visit () e_then in
        let e_else = self#visit () e_else in
        (* [b] holds the return value of the conditional *)
        let b = { b with node = { b.node with mut = true }} in
        let b, e2 = open_binder b e2 in
        let nest_assign = nest_in_return_pos (fun innermost -> {
          node = EAssign ({ node = EOpen (b.node.name, b.node.atom); typ = b.typ }, innermost);
          typ = TUnit
        }) in
        (* Once we find the nested-most return expression, we turn it into an
         * assignment. *)
        let e_then = nest_assign e_then in
        let e_else = nest_assign e_else in
        let e_ifthenelse = {
          node = EIfThenElse (cond, e_then, e_else);
          typ = TUnit
        } in
        ELet (b, { node = EAny; typ = TAny },
          close_binder b (lift 1 ({
            node = ELet (sequence_binding (), e_ifthenelse, lift 1 (self#visit () e2));
            typ = e2.typ
          })))
    | ESwitch (e, branches), None ->
        let b = { b with node = { b.node with mut = true }} in
        let b, e2 = open_binder b e2 in
        let nest_assign = nest_in_return_pos (fun innermost -> {
          node = EAssign ({ node = EOpen (b.node.name, b.node.atom); typ = b.typ }, innermost);
          typ = TUnit
        }) in
        let branches = List.map (fun (tag, e) -> tag, nest_assign (self#visit () e)) branches in
        let e_switch = {
          node = ESwitch (e, branches);
          typ = TUnit
        } in
        ELet (b, { node = EAny; typ = TAny },
          close_binder b (lift 1 ({
            node = ELet (sequence_binding (), e_switch, lift 1 (self#visit () e2));
            typ = e2.typ
        })))
    | _ ->
        (* There are no more nested lets at this stage *)
        ELet (b, self#visit () e1, self#visit () e2)

end

(* No left-nested let-bindings ************************************************)

let nest (lhs: (binder * expr) list) (e2: expr) =
  List.fold_right (fun (binder, e1) e2 ->
    let e2 = close_binder binder e2 in
    { node = ELet (binder, e1, e2); typ = e2.typ }
  ) lhs e2

let mk_binding name t =
  let b = fresh_binder name t in
  b,
  { node = EOpen (b.node.name, b.node.atom); typ = t }

(** Generates "let [[name]]: [[t]] = [[e]] in [[name]]" *)
let mk_named_binding name t e =
  let b, ref = mk_binding name t in
  b,
  { node = e; typ = t },
  ref

(* This function returns an expression that can successfully be translated as a
 * C* statement, after going through let-if-to-assign conversion.
 * - This function shall be called wherever statements are expected (function
 *   bodies; then/else branches; branches of switches).
 * - It returns a series of let-bindings nested over an expression in terminal
 *   position.
 * - It guarantees that if-then-else nodes appear either in statement position,
 *   or immediately under a let-binding, meaning they will undergo
 *   let-if-to-assign conversion.
 * - This function is type-directed; if the expression returns unit, then an
 *   if-then-else or a switch is allowed in terminal position. *)
let rec hoist_stmt e =
  let mk node = { e with node } in
  match e.node with
  | EApp (e, es) ->
      (* A call is allowed in terminal position regardless of whether it has
       * type unit (generates a statement) or not (generates a [EReturn expr]). *)
      let lhs, e = hoist_expr false e in
      let lhss, es = List.split (List.map (hoist_expr false) es) in
      let lhs = lhs @ List.flatten lhss in
      nest lhs (mk (EApp (e, es)))

  | ELet (binder, e1, e2) ->
      (* When building a statement, let-bindings may nest right but not left. *)
      let lhs, e1 = hoist_expr true e1 in
      let binder, e2 = open_binder binder e2 in
      let e2 = hoist_stmt e2 in
      nest lhs (mk (ELet (binder, e1, close_binder binder e2)))

  | EIfThenElse (e1, e2, e3) ->
      if e.typ = TUnit then
        let lhs, e1 = hoist_expr false e1 in
        let e2 = hoist_stmt e2 in
        let e3 = hoist_stmt e3 in
        nest lhs (mk (EIfThenElse (e1, e2, e3)))
      else
        let lhs, e = hoist_expr false e in
        nest lhs e

  | ESwitch (e1, branches) ->
      if e.typ = TUnit then
        let lhs, e1 = hoist_expr false e1 in
        let branches = List.map (fun (tag, e2) -> tag, hoist_stmt e2) branches in
        nest lhs (mk (ESwitch (e1, branches)))
      else
        let lhs, e = hoist_expr false e in
        nest lhs e

  | EWhile (e1, e2) ->
      (* All of the following cases are valid statements (their return type is
       * [TUnit]. *)
      assert (e.typ = TUnit);
      let lhs, e1 = hoist_expr false e1 in
      let e2 = hoist_stmt e2 in
      nest lhs (mk (EWhile (e1, e2)))

  | EAssign (e1, e2) ->
      assert (e.typ = TUnit);
      let lhs1, e1 = hoist_expr false e1 in
      let lhs2, e2 = hoist_expr false e2 in
      nest (lhs1 @ lhs2) (mk (EAssign (e1, e2)))

  | EBufWrite (e1, e2, e3) ->
      assert (e.typ = TUnit);
      let lhs1, e1 = hoist_expr false e1 in
      let lhs2, e2 = hoist_expr false e2 in
      let lhs3, e3 = hoist_expr false e3 in
      nest (lhs1 @ lhs2 @ lhs3) (mk (EBufWrite (e1, e2, e3)))

  | EBufBlit (e1, e2, e3, e4, e5) ->
      assert (e.typ = TUnit);
      let lhs1, e1 = hoist_expr false e1 in
      let lhs2, e2 = hoist_expr false e2 in
      let lhs3, e3 = hoist_expr false e3 in
      let lhs4, e4 = hoist_expr false e4 in
      let lhs5, e5 = hoist_expr false e5 in
      nest (lhs1 @ lhs2 @ lhs3 @ lhs4 @ lhs5) (mk (EBufBlit (e1, e2, e3, e4, e5)))

  | EReturn e ->
      let lhs, e = hoist_expr false e in
      nest lhs (mk (EReturn e))

  | EMatch _ ->
      failwith "[hoist_t]: EMatch not properly desugared"

  | ETuple _ ->
      failwith "[hoist_t]: ETuple not properly desugared"

  | ESequence _ ->
      failwith "[hoist_t]: sequences should've been translated as let _ ="

  | _ ->
      let lhs, e = hoist_expr false e in
      nest lhs e

(* This function returns an expression that can be successfully translated as a
 * C* expression. *)
and hoist_expr under_stmt_let e =
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
  | EEnum _
  | EOp _ ->
      [], e

  | EApp (e, es) ->
      (* TODO: assert that in the case of a lazily evaluated boolean operator,
       * there are no intermediary let-bindings there... or does F* guarantee
       * that no effectful computations can occur there? *)
      let lhs, e = hoist_expr false e in
      let lhss, es = List.split (List.map (hoist_expr false) es) in
      (* TODO: reverse the order and use [rev_append] here *)
      let lhs = lhs @ List.flatten lhss in
      lhs, mk (EApp (e, es))

  | ELet (binder, e1, e2) ->
      let lhs1, e1 = hoist_expr true e1 in
      let binder, e2 = open_binder binder e2 in
      (* The caller (e.g. [hoist_t]) takes care, via [nest], of closing this
       * binder. *)
      let lhs2, e2 = hoist_expr false e2 in
      lhs1 @ [ binder, e1 ] @ lhs2, e2

  | EIfThenElse (e1, e2, e3) ->
      let t = e.typ in
      let lhs1, e1 = hoist_expr false e1 in
      let e2 = hoist_stmt e2 in
      let e3 = hoist_stmt e3 in
      if under_stmt_let then
        lhs1, mk (EIfThenElse (e1, e2, e3))
      else
        let b, body, cont = mk_named_binding "ite" t (EIfThenElse (e1, e2, e3)) in
        lhs1 @ [ b, body ], cont

  | ESwitch (e1, branches) ->
      let t = e.typ in
      let lhs, e1 = hoist_expr false e1 in
      let branches = List.map (fun (tag, e) -> tag, hoist_stmt e) branches in
      if under_stmt_let then
        lhs, mk (ESwitch (e1, branches))
      else
        let b, body, cont = mk_named_binding "sw" t (ESwitch (e1, branches)) in
        lhs @ [ b, body ], cont

  | EWhile (e1, e2) ->
      let lhs1, e1 = hoist_expr false e1 in
      let e2 = hoist_stmt e2 in
      if under_stmt_let then
        lhs1, mk (EWhile (e1, e2))
      else
        let b = fresh_binder "_" TUnit in
        let b = { b with node = { b.node with meta = Some MetaSequence }} in
        lhs1 @ [ b, mk (EWhile (e1, e2)) ], mk EUnit

  | EAssign (e1, e2) ->
      let lhs1, e1 = hoist_expr false e1 in
      let lhs2, e2 = hoist_expr false e2 in
      if under_stmt_let then
        lhs1 @ lhs2, mk (EAssign (e1, e2))
      else
        let b = fresh_binder "_" TUnit in
        let b = { b with node = { b.node with meta = Some MetaSequence }} in
        lhs1 @ lhs2 @ [ b, mk (EAssign (e1, e2)) ], mk EUnit

  | EBufCreate (e1, e2) ->
      let t = e.typ in
      let lhs1, e1 = hoist_expr false e1 in
      let lhs2, e2 = hoist_expr false e2 in
      if under_stmt_let then
        lhs1 @ lhs2, mk (EBufCreate (e1, e2))
      else
        let b, body, cont = mk_named_binding "buf" t (EBufCreate (e1, e2)) in
        lhs1 @ lhs2 @ [ b, body ], cont

  | EBufCreateL es ->
      let t = e.typ in
      let lhs, es = List.split (List.map (hoist_expr false) es) in
      let lhs = List.flatten lhs in
      if under_stmt_let then
        lhs, mk (EBufCreateL es)
      else
        let b, body, cont = mk_named_binding "buf" t (EBufCreateL es) in
        lhs @ [ b, body ], cont

  | EBufRead (e1, e2) ->
      let lhs1, e1 = hoist_expr false e1 in
      let lhs2, e2 = hoist_expr false e2 in
      lhs1 @ lhs2, mk (EBufRead (e1, e2))

  | EBufWrite (e1, e2, e3) ->
      let lhs1, e1 = hoist_expr false e1 in
      let lhs2, e2 = hoist_expr false e2 in
      let lhs3, e3 = hoist_expr false e3 in
      let lhs = lhs1 @ lhs2 @ lhs3 in
      if under_stmt_let then
        lhs, mk (EBufWrite (e1, e2, e3))
      else
        let b = fresh_binder "_" TUnit in
        let b = { b with node = { b.node with meta = Some MetaSequence }} in
        lhs @ [ b, mk (EBufWrite (e1, e2, e3)) ], mk EUnit

  | EBufBlit (e1, e2, e3, e4, e5) ->
      let lhs1, e1 = hoist_expr false e1 in
      let lhs2, e2 = hoist_expr false e2 in
      let lhs3, e3 = hoist_expr false e3 in
      let lhs4, e4 = hoist_expr false e4 in
      let lhs5, e5 = hoist_expr false e5 in
      let lhs = lhs1 @ lhs2 @ lhs3 @ lhs4 @ lhs5 in
      if under_stmt_let then
        lhs, mk (EBufBlit (e1, e2, e3, e4, e5))
      else
        let b = fresh_binder "_" TUnit in
        let b = { b with node = { b.node with meta = Some MetaSequence }} in
        lhs @ [ b, mk (EBufBlit (e1, e2, e3, e4, e5)) ], mk EUnit

  | EBufFill (e1, e2, e3) ->
      let lhs1, e1 = hoist_expr false e1 in
      let lhs2, e2 = hoist_expr false e2 in
      let lhs3, e3 = hoist_expr false e3 in
      let lhs = lhs1 @ lhs2 @ lhs3 in
      if under_stmt_let then
        lhs, mk (EBufFill (e1, e2, e3))
      else
        let b = fresh_binder "_" TUnit in
        let b = { b with node = { b.node with meta = Some MetaSequence }} in
        lhs @ [ b, mk (EBufFill (e1, e2, e3)) ], mk EUnit

  | EBufSub (e1, e2) ->
      let lhs1, e1 = hoist_expr false e1 in
      let lhs2, e2 = hoist_expr false e2 in
      lhs1 @ lhs2, mk (EBufSub (e1, e2))

  | ECast (e, t) ->
      let lhs, e = hoist_expr false e in
      lhs, mk (ECast (e, t))

  | EField (e, f) ->
      let lhs, e = hoist_expr false e in
      lhs, mk (EField (e, f))

  | EFlat fields ->
      let lhs, fields = List.split (List.map (fun (ident, expr) ->
        let lhs, expr = hoist_expr false expr in
        lhs, (ident, expr)
      ) fields) in
      List.flatten lhs, mk (EFlat fields)

  | ECons (ident, es) ->
      let lhs, es = List.split (List.map (hoist_expr false) es) in
      List.flatten lhs, mk (ECons (ident, es))

  | ETuple _ ->
      failwith "[hoist_t]: ETuple not properly desugared"

  | EMatch _ ->
      failwith "[hoist_t]: EMatch"

  | ESequence _ ->
      fatal_error "[hoist_t]: sequences should've been translated as let _ ="

  | EReturn _ ->
      raise_error (Unsupported "[return] expressions should only appear in statement position")

let hoist = object
  inherit ignore_everything
  inherit [_] map

  method dfunction () cc flags ret name binders expr =
    (* TODO: no nested let-bindings in top-level value declarations either *)
    let binders, expr = open_binders binders expr in
    let expr = hoist_stmt expr in
    let expr = close_binders binders expr in
    DFunction (cc, flags, ret, name, binders, expr)
end


(* Relax the criterion a little bit for terminal positions ********************)

let rec fixup_return_pos e =
  (* We know how to insert returns and won't need assignments for things that
   * are in terminal position. *)
  with_type e.typ (match e.node with
  | ELet (_, ({ node = (EIfThenElse _ | ESwitch _); _ } as e), { node = EBound 0; _ }) ->
      (fixup_return_pos e).node
  | EIfThenElse (e1, e2, e3) ->
      EIfThenElse (e1, fixup_return_pos e2, fixup_return_pos e3)
  | ESwitch (e1, branches) ->
      ESwitch (e1, List.map (fun (t, e) -> t, fixup_return_pos e) branches)
  | ELet (b, e1, e2) ->
      ELet (b, e1, fixup_return_pos e2)
  | e ->
      e
  )

let fixup_hoist = object
  inherit ignore_everything
  inherit [_] map

  method dfunction () cc flags ret name binders expr =
    DFunction (cc, flags, ret, name, binders, fixup_return_pos expr)
end


(* No partial applications ****************************************************)

let eta_expand = object
  inherit [_] map
  inherit ignore_everything

  method dglobal () flags name t body =
    (* TODO: eta-expand partially applied functions *)
    match t with
    | TArrow _ ->
        let tret, targs = flatten_arrow t in
        let n = List.length targs in
        let binders, args = List.split (List.mapi (fun i t ->
          with_type t { name = Printf.sprintf "x%d" i; mut = false; mark = ref 0; meta = None; atom = Atom.fresh () },
          { node = EBound (n - i - 1); typ = t }
        ) targs) in
        let body = { node = EApp (body, args); typ = tret } in
        DFunction (None, flags, tret, name, binders, body)
    | _ ->
        DGlobal (flags, name, t, body)
end


(* Make top-level names C-compatible using a global translation table **********)

let skip_prefix prefix =
  List.exists ((=) (String.concat "." prefix)) !Options.no_prefix

let target_c_name lident =
  if skip_prefix (fst lident) then
    snd lident
  else
    string_of_lident lident

let record_name lident =
  [], GlobalNames.record (string_of_lident lident) (target_c_name lident)

let record_toplevel_names = object
  inherit [_] map

  method dglobal () flags name t body =
    DGlobal (flags, record_name name, t, body)

  method dfunction () cc flags ret name args body =
    DFunction (cc, flags, ret, record_name name, args, body)

  method dexternal () cc name t =
    DExternal (cc, record_name name, t)

  method dtype () name n t =
    DType (record_name name, n, t)

  method dtypeenum () tags =
    Enum (List.map record_name tags)
end

let t lident =
  [], GlobalNames.translate (string_of_lident lident) (target_c_name lident)

let replace_references_to_toplevel_names = object(self)
  inherit [unit] map

  method tapp () lident args =
    TApp (t lident, List.map (self#visit_t ()) args)

  method tqualified () lident =
    TQualified (t lident)

  method equalified () _ lident =
    EQualified (t lident)

  method dglobal () flags name typ body =
    DGlobal (flags, t name, self#visit_t () typ, self#visit () body)

  method dfunction () cc flags ret name args body =
    DFunction (cc, flags, self#visit_t () ret, t name, self#binders () args, self#visit () body)

  method dexternal () cc name typ =
    DExternal (cc, t name, self#visit_t () typ)

  method dtype () name n d =
    DType (t name, n, self#type_def () (Some name) d)

  method dtypeenum () tags =
    Enum (List.map t tags)

  method penum () _ name =
    PEnum (t name)

  method eenum () _ name =
    EEnum (t name)

  method eswitch () _ e branches =
    ESwitch (self#visit () e, List.map (fun (tag, e) -> t tag, self#visit () e) branches)
end


(* Everything composed together ***********************************************)

let simplify1 (files: file list): file list =
  let files = visit_files () record_toplevel_names files in
  let files = visit_files () replace_references_to_toplevel_names files in
  let files = visit_files () eta_expand files in
  let files = visit_files () wrapping_arithmetic files in
  files

let simplify2 (files: file list): file list =
  let files = visit_files () sequence_to_let files in
  let files = visit_files () hoist files in
  let files = visit_files () fixup_hoist files in
  let files = visit_files () let_if_to_assign files in
  let files = visit_files () let_to_sequence files in
  files

let simplify (files: file list): file list =
  let files = simplify1 files in
  let files = simplify2 files in
  files

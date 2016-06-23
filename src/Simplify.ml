(** This module rewrites the original AST to send it into Low*, the subset we
 * know how to translate to C. *)

open Ast
open DeBruijn

(* Some helpers ***************************************************************)

let visit_decl (env: 'env) mapper = function
  | DFunction (ret, name, binders, expr) ->
      mapper#dfunction env ret name binders expr
  | DTypeAlias t ->
      DTypeAlias t

let visit_program (env: 'env) mapper (program: program) =
  List.map (visit_decl env mapper) program

let visit_file (env: 'env) mapper (file: file) =
  let name, program = file in
  name, visit_program env mapper program

let visit_files (env: 'env) (mapper: < dfunction: 'env -> typ -> ident -> binder list -> expr -> decl; .. >) (files: file list) =
  List.map (visit_file env mapper) files


(* Count the number of occurrences of each variable ***************************)

class count_use = object

  inherit [binder list] map

  method extend env binder =
    binder :: env

  method ebound env i =
    let b = List.nth env i in
    b.mark <- b.mark + 1;
    EBound i

end


(* F* extraction generates these degenerate cases *****************************)

class dummy_match = object (self)

  inherit [unit] map

  method ematch () e branches =
    match e, branches with
    | EUnit, [ PUnit, body ] ->
        self # visit () body
    | _, [ PBool true, b1; PVar v, b2 ] when v.mark = 0 ->
        let b2 = open_binder v b2 in
        EIfThenElse (e, b1, b2)
    | _ ->
        EMatch (e, self # branches () branches)

end


(* Get wraparound semantics for arithemtic operations using casts to uint_* ***)

class wrapping_arithmetic = object (self)

  inherit [unit] map

  method eapp () e es =
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


(* No left-nested let-bindings ************************************************)

let nest (lhs: (binder * expr) list) (e2: expr) =
  List.fold_right (fun (binder, e1) e2 ->
    let e2 = close binder 0 e2 in
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
  | EBound _
  | EOpen _
  | EQualified _
  | EConstant _
  | EUnit
  | EPushFrame | EPopFrame
  | EOp _ ->
      e

  | EApp (e, es) ->
      let lhs, e = hoist e in
      let lhss, es = List.split (List.map hoist es) in
      let lhs = lhs @ List.flatten lhss in
      nest lhs (EApp (e, es))

  | ELet (binder, e1, e2) ->
      (* At top-level, bindings may nest on the right-hand side of let-bindings,
       * but not on the left-hand side. *)
      let lhs, e1 = hoist e1 in
      let e2 = open_binder binder e2 in
      let e2 = hoist_t e2 in
      nest lhs (ELet (binder, e1, close_binder binder e2))

  | EIfThenElse (e1, e2, e3) ->
      let lhs, e1 = hoist e1 in
      let e2 = hoist_t e2 in
      let e3 = hoist_t e3 in
      nest lhs (EIfThenElse (e1, e2, e3))

  | ESequence es ->
      (* At top-level, let-bindings may appear within sequences, as they will be
       * translated into top-level [C.Decl] nodes. *)
      ESequence (List.map hoist_t es)

  | EAssign (e1, e2) ->
      let lhs1, e1 = hoist e1 in
      let lhs2, e2 = hoist e2 in
      nest (lhs1 @ lhs2) (EAssign (e1, e2))

  | EBufCreate (e1, e2) ->
      let lhs1, e1 = hoist e1 in
      let lhs2, e2 = hoist e2 in
      nest (lhs1 @ lhs2) (EBufCreate (e1, e2))

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

(* This traversal guarantees that no let-bindings are left in the visited term.
 * It returns a [(binder * expr) list] of all the hoisted bindings. It is up to
 * the caller to rewrite the bindings somehow and call [close_binder] on the
 * [binder]s. The bindings are ordered in the evaluation order (i.e. the first
 * binding returned should be evaluated first). *)
and hoist e =
  match e with
  | EBound _
  | EOpen _
  | EQualified _
  | EConstant _
  | EUnit
  | EPushFrame | EPopFrame
  | EOp _ ->
      [], e

  | EApp (e, es) ->
      let lhs, e = hoist e in
      let lhss, es = List.split (List.map hoist es) in
      let lhs = lhs @ List.flatten lhss in
      lhs, EApp (e, es)

  | ELet (binder, e1, e2) ->
      let lhs1, e1 = hoist e1 in
      let e2 = open_binder binder e2 in
      (* The caller (e.g. [hoist_t]) takes care, via [nest], of closing this
       * binder. *)
      let lhs2, e2 = hoist e2 in
      (binder, e1) :: lhs1 @ lhs2, e2

  | EIfThenElse _ ->
      failwith "[hoist]: EIfThenElse not properly lifted"

  | ESequence es ->
      let lhs, es = List.split (List.map hoist es) in
      List.flatten lhs, ESequence es

  | EAssign (e1, e2) ->
      let lhs1, e1 = hoist e1 in
      let lhs2, e2 = hoist e2 in
      lhs1 @ lhs2, EAssign (e1, e2)

  | EBufCreate (e1, e2) ->
      let lhs1, e1 = hoist e1 in
      let lhs2, e2 = hoist e2 in
      lhs1 @ lhs2, EBufCreate (e1, e2)

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


(* Everything composed together ***********************************************)

let simplify (files: file list): file list =
  let files = visit_files [] (new count_use) files in
  let files = visit_files () (new dummy_match) files in
  let files = visit_files () (new wrapping_arithmetic) files in
  let files = visit_files () (object
    method dfunction () ret name binders expr =
      let expr = open_function_binders binders expr in
      let expr = hoist_t expr in
      let expr = close_function_binders binders expr in
      DFunction (ret, name, binders, expr)
  end) files in
  files

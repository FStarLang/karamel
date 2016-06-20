(** Various peephole optimizations *)

open Ast
open DeBruijn

(* Some helpers ***************************************************************)

let visit_decl (env: 'env) (mapper: 'env -> expr -> expr) = function
  | DFunction (ret, name, binders, expr) ->
      let expr = open_function_binders binders expr in
      let expr = mapper env expr in
      let expr = close_function_binders binders expr in
      DFunction (ret, name, binders, expr)
  | DTypeAlias t ->
      DTypeAlias t

let visit_program (env: 'env) (mapper: 'env -> expr -> expr) (program: program) =
  List.map (visit_decl env mapper) program

let visit_file (env: 'env) (mapper: 'env -> expr -> expr) (file: file) =
  let name, program = file in
  name, visit_program env mapper program

let visit_files (env: 'env) (mapper: 'env -> expr -> expr) (files: file list) =
  List.map (visit_file env mapper) files


(* The peephole optimizations themselves **************************************)

class dummymatch = object (self)

  inherit [unit] map

  method ematch () e branches =
    match e, branches with
    | EUnit, [ PUnit, body ] ->
        self # visit () body
    | _ ->
        EMatch (e, self # branches () branches)

end

(* No left-nested let-bindings ************************************************)

let nest (lhs: (binder * expr) list) (e2: expr) =
  List.fold_right (fun (binder, e1) e2 ->
    let e2 = close binder 0 e2 in
    ELet (binder, e1, e2)
  ) lhs e2

(* A toplevel context is one where let-bindings may appear; therefore, this
 * function may return an [ELet] node. *)
let rec hoist_t e =
  match e with
  | EBound _
  | EOpen _
  | EQualified _
  | EConstant _
  | EUnit
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
      nest lhs (close_binder binder (ELet (binder, e1, e2)))

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

  | EBufSub (e1, e2, e3) ->
      let lhs1, e1 = hoist e1 in
      let lhs2, e2 = hoist e2 in
      let lhs3, e3 = hoist e3 in
      nest (lhs1 @ lhs2 @ lhs3) (EBufSub (e1, e2, e3))

  | EMatch _ ->
      failwith "[hoist_t]: EMatch not properly desugared"

(* This traversal guarantees that none of the sub-terms contains a let-binding.
 * It returns a [(binder * expr) list] of all the hoisted terms. *)
and hoist e =
  match e with
  | EBound _
  | EOpen _
  | EQualified _
  | EConstant _
  | EUnit
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
      (* [nest] will take care of closing this binder. *)
      let lhs2, e2 = hoist e2 in
      (binder, e1) :: lhs1 @ lhs2, e2

  | EIfThenElse (e1, e2, e3) ->
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

  | EBufSub (e1, e2, e3) ->
      let lhs1, e1 = hoist e1 in
      let lhs2, e2 = hoist e2 in
      let lhs3, e3 = hoist e3 in
      lhs1 @ lhs2 @ lhs3, EBufSub (e1, e2, e3)

  | EMatch _ ->
      failwith "[hoist_t]: EMatch"

(* Everything composed together ***********************************************)

let simplify (files: file list): file list =
  let files = visit_files () (new dummymatch # visit) files in
  let files = visit_files () (fun () -> hoist_t) files in
  files

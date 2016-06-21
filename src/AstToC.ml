(** Translation from Low* to C* *)

(** In order to qualify as a Low* AST (and hence be eligible for translation),
 * the following criteria must be satisfied:
 * - no nested let-bindings;
 * - no matches (at the moment);
 * - in the body of let-bindings, the test expression of conditionals, the
 *   right-hand side of assignments, in all buffer expressions, in function
 *   arguments the following are disallowed:
 *   + sequence expressions
 *   + conditionals
 *   + assignments
 *   + buffer writes
 *   + let-bindings
 *   + impure function calls
 * - the first subexpression of buffer reads, writes and subs must be a
 *   qualified or local name.
 *)

open Ast

let map_flatten f l = List.flatten (List.map f l)

type env = {
  names: ident list;
  in_block: ident list;
}

let empty: env = {
  names = [];
  in_block = [];
}

let reset_block env = {
  env with in_block = []
}

let push env binder = C.{
  names = binder.name :: env.names;
  in_block = binder.name :: env.in_block
}

let find env i =
  List.nth env.names i

(* If the name already exists in the block, then we have to pick a new one for
 * it. But we should make sure we don't accidentally shadow an existing name
 * defined in another block higher up. This is, naturally, a conservative
 * choice. *)
let ensure_fresh env name =
  if List.exists ((=) name) env.in_block then
    let i = ref 0 in
    let mk () = name ^ string_of_int !i in
    while List.exists ((=) (mk ())) env.names do
      incr i
    done;
    mk ()
  else
    name


let rec translate_expr env = function
  | EBound var ->
      C.Var (find env var)
  | EOpen { name; typ } ->
      failwith "[AstToC.translate_expr EOpen]: invalid argument"
  | EQualified lident ->
      C.Qualified lident
  | EConstant c ->
      C.Constant c
  | EApp (e, es) ->
      C.Call (translate_expr env e, List.map (translate_expr env) es)
  | EBufCreate (e1, e2) ->
      C.BufCreate (translate_expr env e1, translate_expr env e2)
  | EBufRead (e1, e2) ->
      C.BufRead (translate_expr env e1, translate_expr env e2)
  | EBufSub (e1, e2, e3) ->
      C.BufSub (translate_expr env e1, translate_expr env e2, translate_expr env e3)
  | EOp (c, _) ->
      C.Op c
  | ECast (e, t) ->
      C.Cast (translate_expr env e, translate_type env t)
  | EUnit ->
      failwith "[AstToC.translate_expr EUnit]: not implemented"
  | ELet _ ->
      failwith "[AstToC.translate_expr ELet]: not implemented"
  | EIfThenElse _ ->
      failwith "[AstToC.translate_expr EIfThenElse]: not implemented"
  | ESequence _ ->
      failwith "[AstToC.translate_expr ESequence]: not implemented"
  | EAssign _ ->
      failwith "[AstToC.translate_expr EAssign]: not implemented"
  | EBufWrite _ ->
      failwith "[AstToC.translate_expr EBufWrite]: not implemented"
  | EMatch _ ->
      failwith "[AstToC.translate_expr EMatch]: not implemented"


and collect (env, acc) = function
  | ELet (binder, e1, e2) ->
      let env, binder = translate_and_push_binder env binder in
      let acc = C.Decl (binder, translate_expr env e1) :: acc in
      collect (env, acc) e2

  | EIfThenElse (e1, e2, e3) ->
      let e = C.IfThenElse (translate_expr env e1, translate_block env e2, translate_block env e3) in
      env, e :: acc

  | ESequence es ->
      List.fold_left collect (env, acc) es

  | EAssign (e1, e2) ->
      let e = C.Assign (translate_expr env e1, translate_expr env e2) in
      env, e :: acc

  | EBufWrite (e1, e2, e3) ->
      let e = C.BufWrite (translate_expr env e1, translate_expr env e2, translate_expr env e3) in
      env, e :: acc

  | EMatch _ ->
      failwith "[AstToC.collect EMatch]: not implemented"

  | EUnit ->
      env, acc

  | e ->
      let e = C.Ignore (translate_expr env e) in
      env, e :: acc


and translate_block env e =
  List.rev (snd (collect (reset_block env, []) e))


(** If the return type is != [C.Void], then the head of the accumulator is the
 * final value returned by the function. Only two nodes may have non-void return
 * types; the first one is [C.Ignore] and we make it a proper [C.Return]. The
 * second one is [C.IfThenElse]; but we do not allow conditionals in expressions
 * in C*; so, [Simplify] and other passes must guarantees all [EIfThenElse] are
 * transformed to have type [TUnit].
 *)
and translate_function_block env e t =
  let stmts = snd (collect (reset_block env, []) e) in
  match t, stmts with
  | C.Void, _ ->
      (* TODO: type aliases *)
      List.rev stmts

  | _, C.Ignore e :: stmts ->
      List.rev (C.Return e :: stmts)

  | _, _ ->
      failwith "[translate_function_block]: violated invariant"


and translate_type env = function
  | TInt w ->
      C.Int w
  | TBuf t ->
      C.Pointer (translate_type env t)
  | TUnit ->
      C.Void
  | TAlias name ->
      C.Named name


and translate_and_push_binders env binders =
  let env, acc = List.fold_left (fun (env, acc) binder ->
    let env, binder = translate_and_push_binder env binder in
    env, binder :: acc
  ) (env, []) binders in
  env, List.rev acc

and translate_and_push_binder env binder =
  let binder = {
    C.name = ensure_fresh env binder.name;
    typ = translate_type env binder.typ
  } in
  push env binder, binder

and translate_declaration env d: C.decl =
  match d with
  | DFunction (t, name, binders, body) ->
      let t = translate_type env t in
      let env, binders = translate_and_push_binders env binders in
      let body = translate_function_block env body t in
      C.Function (t, name, binders, body)

  | DTypeAlias (name, t) ->
      C.TypeAlias (name, translate_type env t)


and translate_program decls =
  List.map (translate_declaration empty) decls

and translate_file (name, program) =
  name, translate_program program

and translate_files files =
  List.map translate_file files

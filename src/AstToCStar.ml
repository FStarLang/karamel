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
open Idents
open Error
let pexpr = PrintAst.pexpr
let ptyp = PrintAst.ptyp

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

let push env binder = CStar.{
  names = binder.name :: env.names;
  in_block = binder.name :: env.in_block
}

let find env i =
  List.nth env.names i

(* Freshness is a pain. Name conflicts can arise from the following situations.

  ML: shadowing within your own block
    let x = ... in
    let x = ... x ... in
  C:
    int x = ...;
    int x1 = ... x ...;
  This is caught by the (List.exists ...) test.

  ML: shadowing outside of your own block WITH references to the shadowed variable
    fun x ->
      let x = x + 1 in
  bad C:
    void f(x) {
      int x = x + 1;
  correct C:
    void f(x) {
      int x1 = x + 1;
  This is caught by the visitor that checks whether the body of the definition
  mentions ANY variable by the same name.

  ML: shadowing outside of your own block WITHOUT references to the shadowed variable
    fun x ->
      let x = 1 in
  C:
    void f(x) {
      int x = 1;
  This is fine.
*)
let ensure_fresh env name body =
  let tricky_shadowing_see_comment_above name =
    match body with
    | None ->
        false
    | Some body ->
        let r = ref false in
        ignore ((object
          inherit [string list] map
          method extend env binder =
            Printf.eprintf "extend %s\n" binder.name;
            binder.name :: env
          method ebound env i =
            r := !r || name = List.nth env i;
            EBound i
        end) # visit env.names body);
        !r
  in
  mk_fresh name (fun tentative ->
    tricky_shadowing_see_comment_above tentative || List.exists ((=) tentative) env.in_block)


let rec translate_expr env e =
  match e with
  | EBound var ->
      CStar.Var (find env var)
  | EQualified lident ->
      CStar.Qualified lident
  | EConstant c ->
      CStar.Constant c
  | EApp (e, es) ->
      CStar.Call (translate_expr env e, List.map (translate_expr env) es)
  | EBufCreate (e1, e2) ->
      CStar.BufCreate (translate_expr env e1, translate_expr env e2)
  | EBufRead (e1, e2) ->
      CStar.BufRead (translate_expr env e1, translate_expr env e2)
  | EBufSub (e1, e2) ->
      CStar.BufSub (translate_expr env e1, translate_expr env e2)
  | EOp (c, _) ->
      CStar.Op c
  | ECast (e, t) ->
      CStar.Cast (translate_expr env e, translate_type env t)
  | EOpen _ | EPopFrame | EPushFrame | EBufBlit _ | EAbort ->
      throw_error "[AstToCStar.translate_expr]: invalid argument (%a)" pexpr e
  | EUnit ->
      CStar.Constant (K.UInt8, "0")
  | EAny ->
      CStar.Any
  | ELet _ ->
      throw_error "[AstToCStar.translate_expr ELet]: not implemented"
  | EIfThenElse _ ->
      throw_error "[AstToCStar.translate_expr EIfThenElse]: not implemented"
  | ESequence _ ->
      throw_error "[AstToCStar.translate_expr ESequence]: not implemented"
  | EAssign _ ->
      throw_error "[AstToCStar.translate_expr EAssign]: not implemented"
  | EBufWrite _ ->
      throw_error "[AstToCStar.translate_expr EBufWrite]: not implemented"
  | EMatch _ ->
      throw_error "[AstToCStar.translate_expr EMatch]: not implemented"
  | EBool b ->
      CStar.Bool b


and collect (env, acc) = function
  | ELet (binder, e1, e2) ->
      let env, binder = translate_and_push_binder env binder (Some e1)
      and e1 = translate_expr env e1 in
      let acc = CStar.Decl (binder, e1) :: acc in
      collect (env, acc) e2

  | EIfThenElse (e1, e2, e3, _) ->
      let e = CStar.IfThenElse (translate_expr env e1, translate_block env e2, translate_block env e3) in
      env, e :: acc

  | ESequence es ->
      List.fold_left (fun (_, acc) -> collect (env, acc)) (env, acc) es

  | EAssign (e1, e2) ->
      let e = CStar.Assign (translate_expr env e1, translate_expr env e2) in
      env, e :: acc

  | EBufBlit (e1, e2, e3, e4, e5) ->
      let e = CStar.BufBlit (translate_expr env e1, translate_expr env e2, translate_expr env e3, translate_expr env e4, translate_expr env e5) in
      env, e :: acc

  | EBufWrite (e1, e2, e3) ->
      let e = CStar.BufWrite (translate_expr env e1, translate_expr env e2, translate_expr env e3) in
      env, e :: acc

  | EMatch _ ->
      throw_error "[AstToCStar.collect EMatch]: not implemented"

  | EUnit ->
      env, acc

  | EPushFrame ->
      env, CStar.PushFrame :: acc

  | EPopFrame ->
      env, CStar.PopFrame :: acc

  | EAbort ->
      env, CStar.Abort :: acc

  | e ->
      let e = CStar.Ignore (translate_expr env e) in
      env, e :: acc


and translate_block env e =
  List.rev (snd (collect (reset_block env, []) e))


(** If the return type is != [CStar.Void], then the head of the accumulator is the
 * final value returned by the function. Only two nodes may have non-void return
 * types; the first one is [CStar.Ignore] and we make it a proper [CStar.Return]. The
 * second one is [CStar.IfThenElse]; but we do not allow conditionals in expressions
 * in C*; so, [Simplify] and other passes must guarantees all [EIfThenElse] are
 * transformed to have type [TUnit].
 *)
and translate_function_block env e t =
  (* The list is returned in reverse order. *)
  let stmts = snd (collect (reset_block env, []) e) in
  match t, stmts with
  | CStar.Void, [] ->
      []
  | _, [] ->
      (* TODO: type aliases for void *)
      throw_error "[translate_function_block]: invariant broken (empty function \
        body, but non-void return type)"
  | _ ->
      match t, List.rev stmts, stmts with
      | CStar.Void, CStar.PushFrame :: _, CStar.PopFrame :: rest ->
          List.tl (List.rev rest)
      | CStar.Pointer CStar.Void, CStar.PushFrame :: _, CStar.Ignore _ :: CStar.PopFrame :: rest -> 
          List.tl (List.rev (CStar.Return CStar.Any :: rest))
      | _, CStar.PushFrame :: _, CStar.PopFrame :: _ ->
          throw_error "[translate_function_block]: invariant broken \
            (well-parenthesized push/pop, but function's return type is not \
            void!)"
      | CStar.Void, stmts, _ ->
          stmts
      | _, _, CStar.Ignore e :: rest ->
          List.rev (CStar.Return e :: rest)
      | _, stmts, CStar.Abort :: _ ->
          stmts
      | _ ->
          throw_error "[translate_function_block]: invariant broken (non-void \
            function does not end with something we can return)"

and translate_return_type env = function
  | TInt w ->
      CStar.Int w
  | TBuf t ->
      CStar.Pointer (translate_type env t)
  | TUnit ->
      CStar.Void
  | TQualified name ->
      CStar.Qualified name
  | TBool ->
      CStar.Bool
  | TAny ->
      CStar.Pointer CStar.Void
  | TArrow _ as t ->
      let ret, args = flatten_arrow t in
      CStar.Function (translate_return_type env ret, List.map (translate_type env) args)
  | TZ ->
      CStar.Z

and translate_type env = function
  | TUnit ->
      CStar.Pointer CStar.Void
  | t ->
      translate_return_type env t

and translate_and_push_binders env binders =
  let env, acc = List.fold_left (fun (env, acc) binder ->
    let env, binder = translate_and_push_binder env binder None in
    env, binder :: acc
  ) (env, []) binders in
  env, List.rev acc

and translate_and_push_binder env binder body =
  let binder = {
    CStar.name = ensure_fresh env binder.name body;
    typ = translate_type env binder.typ
  } in
  push env binder, binder

and translate_declaration env d: CStar.decl =
  let wrap_throw name (comp: CStar.decl Lazy.t) =
    try Lazy.force comp with
    | Error e ->
        throw_error "(in %s) %s" name e
  in

  match d with
  | DFunction (t, name, binders, body) ->
      wrap_throw name (lazy begin
        let t = translate_return_type env t in
        let env, binders = translate_and_push_binders env binders in
        let body = translate_function_block env body t in
        CStar.Function (t, name, binders, body)
      end)

  | DTypeAlias (name, t) ->
      CStar.TypeAlias (name, translate_type env t)

  | DGlobal (name, t, body) ->
      CStar.Global (name, translate_type env t, translate_expr env body)


and translate_program decls =
  List.map (translate_declaration empty) decls

and translate_file (name, program) =
  name, translate_program program

and translate_files files =
  KList.filter_map (fun f ->
    try
      Some (translate_file f)
    with Error e ->
      Printf.eprintf "Warning: dropping %s [in ast-to-cstar]: %s\n" (fst f) e;
      None
  ) files

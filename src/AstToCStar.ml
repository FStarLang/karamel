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
open Warnings
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

let pnames buf env =
  match env.names with
  | [] ->
      Buffer.add_string buf "no names!"
  | name :: names ->
      Buffer.add_string buf name;
      List.iter (fun name ->
        Buffer.add_string buf ", ";
        Buffer.add_string buf name
      ) names

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
            binder.name :: env
          method ebound env _ i =
            r := !r || name = List.nth env i;
            EBound i
        end) # visit env.names body);
        !r
  in
  mk_fresh name (fun tentative ->
    tricky_shadowing_see_comment_above tentative || List.exists ((=) tentative) env.in_block)


let rec translate_expr env e =
  match e.node with
  | EBound var ->
      CStar.Var (find env var)
  | EQualified lident ->
      CStar.Qualified lident
  | EConstant c ->
      CStar.Constant c
  | EApp (e, es) ->
      (* Functions that only take a unit take no argument. Functions that only
       * return a unit return void. *)
      let es = match e.mtyp with
        | TArrow (TUnit, _) -> []
        | _ -> es
      in
      CStar.Call (translate_expr env e, List.map (translate_expr env) es)
  | EBufCreate (e1, e2) ->
      CStar.BufCreate (translate_expr env e1, translate_expr env e2)
  | EBufCreateL es ->
      CStar.BufCreateL (List.map (translate_expr env) es)
  | EBufRead (e1, e2) ->
      CStar.BufRead (translate_expr env e1, translate_expr env e2)
  | EBufSub (e1, e2) ->
      CStar.BufSub (translate_expr env e1, translate_expr env e2)
  | EOp (c, _) ->
      CStar.Op c
  | ECast (e, t) ->
      CStar.Cast (translate_expr env e, translate_type env t)
  | EOpen _ | EPopFrame | EPushFrame | EBufBlit _ | EAbort ->
      fatal_error "[AstToCStar.translate_expr]: should not be here (%a)" pexpr e
  | EUnit ->
      CStar.Constant (K.UInt8, "0")
  | EAny ->
      CStar.Any
  | ELet _ ->
      fatal_error "[AstToCStar.translate_expr ELet]: should not be here"
  | EIfThenElse _ ->
      fatal_error "[AstToCStar.translate_expr EIfThenElse]: should not be here"
  | EWhile _ ->
      fatal_error "[AstToCStar.translate_expr EIfThenElse]: should not be here"
  | ESequence _ ->
      fatal_error "[AstToCStar.translate_expr ESequence]: should not be here"
  | EAssign _ ->
      fatal_error "[AstToCStar.translate_expr EAssign]: should not be here"
  | EBufWrite _ ->
      fatal_error "[AstToCStar.translate_expr EBufWrite]: should not be here"
  | EMatch _ ->
      fatal_error "[AstToCStar.translate_expr EMatch]: should not be here"
  | EReturn _ ->
      fatal_error "[AstToCStar.translate_expr EReturn]: should not be here"
  | EBool b ->
      CStar.Bool b
  | EFlat fields ->
      let typ = Checker.assert_qualified Checker.empty e.mtyp in
      CStar.Struct (string_of_lident typ, List.map (fun (name, expr) ->
        Some name, translate_expr env expr
      ) fields)
  | EField (expr, field) ->
      CStar.Field (translate_expr env expr, field)


and collect (env, acc) return_pos e =
  match e.node with
  | ELet (binder, e1, e2) ->
      let env, binder = translate_and_push_binder env binder (Some e1)
      and e1 = translate_expr env e1 in
      let acc = CStar.Decl (binder, e1) :: acc in
      collect (env, acc) return_pos e2

  | EWhile (e1, e2) ->
      let e = CStar.While (translate_expr env e1, translate_block env e2) in
      env, e :: acc

  | EIfThenElse (e1, e2, e3) ->
      let e = CStar.IfThenElse (translate_expr env e1, translate_block env e2, translate_block env e3) in
      env, e :: acc

  | ESequence es ->
      let n = List.length es in
      KList.fold_lefti (fun i (_, acc) e ->
        let return_pos = i = n - 1 && return_pos in
        collect (env, acc) return_pos e
      ) (env, acc) es

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
      fatal_error "[AstToCStar.collect EMatch]: not implemented"

  | EUnit ->
      env, acc

  | EPushFrame ->
      env, CStar.PushFrame :: acc

  | EPopFrame ->
      env, CStar.PopFrame :: acc

  | EAbort ->
      env, CStar.Abort :: acc

  | EReturn e ->
      if e.mtyp = TUnit then
        env, CStar.Return None :: acc
      else
        env, CStar.Return (Some (translate_expr env e)) :: acc

  | _ when return_pos ->
      KPrint.bprintf "inserting a return for t=%a, e=%a\n" ptyp e.mtyp pexpr e;
      if e.mtyp = TUnit then
        env, CStar.Return None :: acc
      else
        env, CStar.Return (Some (translate_expr env e)) :: acc

  | _ ->
      let e = CStar.Ignore (translate_expr env e) in
      env, e :: acc

and translate_block env e =
  List.rev (snd (collect (reset_block env, []) false e))


(** This enforces the push/pop frame invariant. The invariant can be described
 * as follows (the extra cases are here to provide better error messages):
 * - a function may choose not to use push/pop frame (it's a pure computation);
 * - if it chooses to use push/pop frame, then either:
 *   - it starts with push_frame and ends with pop_frame (implies the return type
 *     is void)
 *   - it starts with push_frame and ends with pop_frame, and returns a value
 *     immediately after the pop_frame; this only makes sense if the value
 *     requires no allocations in the current frame, which at the moment we only
 *     guarantee for computation of type any (the result of erasure)
 *)
and translate_function_block env e t =
  (** This function expects an environment where names and in_block have been
   * populated with the function's parameters. *)
  let stmts = snd (collect (env, []) true e) in
  match t, stmts with
  | CStar.Void, [] ->
      []
  | _, [] ->
      (* TODO: type aliases for void *)
      raise_error (BadFrame "empty function body, but non-void return type")
  | _ ->
      match t, List.rev stmts, stmts with
      | CStar.Void, CStar.PushFrame :: _, CStar.PopFrame :: rest ->
          List.tl (List.rev rest)
      | CStar.Pointer CStar.Void, CStar.PushFrame :: _, CStar.Return _ :: CStar.PopFrame :: rest ->
          List.tl (List.rev (CStar.Return (Some CStar.Any) :: rest))
      | CStar.Int _, CStar.PushFrame :: _, ((CStar.Return (Some (CStar.Qualified _))) as e) :: CStar.PopFrame :: rest ->
          List.tl (List.rev (e :: rest))
      | _, CStar.PushFrame :: _, CStar.PopFrame :: _ ->
          raise_error (BadFrame ("well-parenthesized push/pop, but function's \
            return type is not void!)"))
      | _, CStar.PushFrame :: _, _
      | _, _, CStar.PopFrame :: _ ->
          raise_error (BadFrame ("unmatched push/pop_frame"))
      | CStar.Void, stmts, _ ->
          stmts
      | _, stmts, CStar.Return _ :: _
      | _, stmts, CStar.Abort :: _ ->
          stmts
      | _ ->
          raise_error (BadFrame ("non-void function does not end with something we can return"))

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
        raise_error_l (locate name e)
  in

  match d with
  | DFunction (t, name, binders, body) ->
      wrap_throw (string_of_lident name) (lazy begin
        let t = translate_return_type env t in
        assert (env.names = []);
        let env, binders = translate_and_push_binders env binders in
        let body = translate_function_block env body t in
        CStar.Function (t, (string_of_lident name), binders, body)
      end)

  | DTypeAlias (name, t) ->
      CStar.Type (string_of_lident name, translate_type env t)

  | DGlobal (name, t, body) ->
      CStar.Global (string_of_lident name, translate_type env t, translate_expr env body)

  | DTypeFlat (name, fields) ->
      let name = string_of_lident name in
      (* TODO: avoid collisions since "_s" is not going through the name
       * generator *)
      CStar.Type (name, CStar.Struct (Some (name ^ "_s"), List.map (fun (field, (typ, _)) ->
        field, translate_type env typ
      ) fields))

  | DExternal (name, t) ->
      CStar.External (string_of_lident name, translate_type env t)


and translate_program decls =
  List.map (translate_declaration empty) decls

and translate_file (name, program) =
  name, translate_program program

and translate_files files =
  KList.filter_map (fun f ->
    try
      Some (translate_file f)
    with Error e ->
      Warnings.maybe_fatal_error (fst e, Dropping (fst f, e));
      None
  ) files

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
open Location

let pexpr = PrintAst.pexpr
let ptyp = PrintAst.ptyp
let plid = PrintAst.plid

let map_flatten f l = List.flatten (List.map f l)

type env = {
  location: loc list;
  names: ident list;
  in_block: ident list;
}

let locate env loc =
  { env with location = update_location env.location loc }

let empty: env = {
  names = [];
  in_block = [];
  location = [];
}

let reset_block env = {
  env with in_block = []
}

let push env binder = CStar.{
  names = binder.name :: env.names;
  in_block = binder.name :: env.in_block;
  location = env.location
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
            binder.node.name :: env
          method ebound env _ i =
            r := !r || name = List.nth env i;
            EBound i
        end) # visit env.names body);
        !r
  in
  mk_fresh name (fun tentative ->
    tricky_shadowing_see_comment_above tentative ||
    List.exists ((=) tentative) env.in_block)


(** AstToCStar performs a unit-to-void conversion.
 *
 * Functions that TAKE a single unit argument are translated as functions that
 * take zero arguments. If the argument is a EUnit expression, we drop it;
 * otherwise, we use a comma operator to make sure we don't discard the
 * (potential) side effect of the argument, EVEN THOUGH F* guarantees that an
 * effectful argument is hoisted (see [translate_expr]).
 *
 * Function that RETURN a single unit argument are translated as functions that
 * return void; this means that any [EReturn e] where [e] has type unit becomes
 * a [Return None]. If [e] is not a value, we can use a sequence (see
 * [translate_expr] again). If a function that has undergone unit to void
 * conversion appears in an expression, again, a comma expression comes to the
 * rescue.
 *
 * The translation of function types is aware of this, too.
 *)

let rec translate_expr env in_stmt e =
  let translate_expr env e = translate_expr env false e in
  match e.node with
  | EBound var ->
      CStar.Var (find env var)
  | EQualified lident ->
      CStar.Qualified lident
  | EConstant c ->
      CStar.Constant c
  | EApp (e, es) ->
      (* Functions that only take a unit take no argument. *)
      let t, ts = flatten_arrow e.typ in
      let call = match ts, es with
        | [ TUnit ], [ { node = EUnit; _ } ] ->
            CStar.Call (translate_expr env e, [])
        | [ TUnit ], [ e' ] ->
            if is_value e' then
              CStar.Call (translate_expr env e, [])
            else
              CStar.Comma (translate_expr env e', CStar.Call (translate_expr env e, []))
        | _ ->
            CStar.Call (translate_expr env e, List.map (translate_expr env) es)
      in
      (* This function call was originally typed as returning [TUnit], a.k.a.
       * [void*]. However, we optimize these functions to return [void], meaning
       * that we can't take their return value as an expression, since there's
       * no return value. So, if such a function appears in an expression, use a
       * comma operator to provide a placeholder value. This situation arises
       * after erasure of lemmas. *)
      if not in_stmt && t = TUnit then
        CStar.Comma (call, CStar.Any)
      else
        call
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
      fatal_error "[AstToCStar.translate_expr ELet]: should not be here %a" ploc env.location
  | EIfThenElse _ ->
      fatal_error "[AstToCStar.translate_expr EIfThenElse]: should not be here %a" ploc env.location
  | EWhile _ ->
      fatal_error "[AstToCStar.translate_expr EIfThenElse]: should not be here %a" ploc env.location
  | ESequence _ ->
      fatal_error "[AstToCStar.translate_expr ESequence]: should not be here %a" ploc env.location
  | EAssign _ ->
      fatal_error "[AstToCStar.translate_expr EAssign]: should not be here %a" ploc env.location
  | EBufWrite _ ->
      fatal_error "[AstToCStar.translate_expr EBufWrite]: should not be here %a" ploc env.location
  | EMatch _ ->
      fatal_error "[AstToCStar.translate_expr EMatch]: should not be here %a" ploc env.location
  | EReturn _ ->
      fatal_error "[AstToCStar.translate_expr EReturn]: should not be here %a" ploc env.location
  | ECons _ ->
      fatal_error "[AstToCStar.translate_expr ECons]: should not be here %a" ploc env.location
  | ETuple _ ->
      fatal_error "[AstToCStar.translate_expr ETuple]: should not be here %a" ploc env.location
  | EBool b ->
      CStar.Bool b
  | EFlat fields ->
      let typ = Checker.assert_qualified Checker.empty e.typ in
      CStar.Struct (string_of_lident typ, List.map (fun (name, expr) ->
        Some name, translate_expr env expr
      ) fields)
  | EField (expr, field) ->
      CStar.Field (translate_expr env expr, field)


and extract_stmts env e ret_type =
  let rec collect (env, acc) return_pos e =
    match e.node with
    | ELet (binder, e1, e2) ->
        let env, binder = translate_and_push_binder env binder (Some e1)
        and e1 = translate_expr env false e1 in
        let acc = CStar.Decl (binder, e1) :: acc in
        collect (env, acc) return_pos e2

    | EWhile (e1, e2) ->
        let e = CStar.While (translate_expr env false e1, translate_block env false e2) in
        env, e :: acc

    | EIfThenElse (e1, e2, e3) ->
        let e = CStar.IfThenElse (translate_expr env true e1, translate_block env return_pos e2, translate_block env return_pos e3) in
        env, e :: acc

    | ESequence es ->
        let n = List.length es in
        KList.fold_lefti (fun i (_, acc) e ->
          let return_pos = i = n - 1 && return_pos in
          collect (env, acc) return_pos e
        ) (env, acc) es

    | EAssign (e1, e2) ->
        let e = CStar.Assign (translate_expr env true e1, translate_expr env true e2) in
        env, e :: acc

    | EBufBlit (e1, e2, e3, e4, e5) ->
        let e = CStar.BufBlit (translate_expr env true e1, translate_expr env true e2, translate_expr env true e3, translate_expr env true e4, translate_expr env true e5) in
        env, e :: acc

    | EBufWrite (e1, e2, e3) ->
        let e = CStar.BufWrite (translate_expr env true e1, translate_expr env true e2, translate_expr env true e3) in
        env, e :: acc

    | EMatch _ ->
        fatal_error "[AstToCStar.collect EMatch]: not implemented"

    | EPushFrame ->
        env, CStar.PushFrame :: acc

    | EPopFrame ->
        env, CStar.PopFrame :: acc

    | EAbort ->
        env, CStar.Abort :: acc

    | EReturn e ->
        translate_as_return env e acc

    | _ when return_pos ->
        translate_as_return env e acc

    | _ ->
        if is_value e then
          env, acc
        else
          let e = CStar.Ignore (translate_expr env true e) in
          env, e :: acc

  and translate_block env return_pos e =
    List.rev (snd (collect (reset_block env, []) return_pos e))

  and translate_as_return env e acc =
    if ret_type = CStar.Void && is_value e then
      env, CStar.Return None :: acc
    else if ret_type = CStar.Void then
      env, CStar.Return None :: CStar.Ignore (translate_expr env true e) :: acc
    else
      env, CStar.Return (Some (translate_expr env false e)) :: acc

  in

  snd (collect (env, []) true e)

(* Things that will generate warnings such as "left-hand operand of comma
 * expression has no effect". *)
and is_value x =
  match x.node with
  | EBound _
  | EOpen _
  | EQualified _
  | EConstant _
  | EUnit
  | EOp _
  | EBool _
  | EAny
  | EFlat _
  | EField _ ->
      true
  | ECast (e,_) ->
      is_value e
  | _ ->
      false

(** This enforces the push/pop frame invariant. The invariant can be described
 * as follows (the extra cases are here to provide better error messages):
 * - a function may choose not to use push/pop frame (it's a pure computation);
 * - if it chooses to use push/pop frame, then either:
 *   - it starts with push_frame and ends with pop_frame (implies the return type
 *     is void)
 *   - it starts with push_frame and ends with pop_frame, and returns a value
 *     immediately after the pop_frame; F* guarantees that this value is
 *     well-scoped and requires no deep-copy (the user will perform it manually,
 *     if needed)
 *   - it uses push_frame and pop_frame in the middle of the function body... in
 *     which case we check no special invariant
 *)
and translate_function_block env e t =
  (** This function expects an environment where names and in_block have been
   * populated with the function's parameters. *)
  let stmts = extract_stmts env e t in

  (** This just enforces some invariants and drops push/pop frame when they span
   * the entire function body (because it's redundant with the function frame). *)
  match List.rev stmts, stmts with
  | [], _ ->
      if t <> CStar.Void then
        (* TODO: type aliases for void *)
        raise_error (BadFrame "empty function body, but non-void return type");
      []

  | CStar.PushFrame :: _, CStar.PopFrame :: rest ->
      if t <> CStar.Void then
        (* TODO: type aliases for void *)
        raise_error (BadFrame "push/pop spans function body, but return type is not void");
      List.tl (List.rev rest)

  | CStar.PushFrame :: _, e :: CStar.PopFrame :: rest ->
      begin match e with
      | CStar.Return None ->
          if t <> CStar.Void then
            raise_error (BadFrame ("empty return, but return type is not void"))
      | CStar.Return (Some _) ->
          (* Note: we could check that [e] is a value at this stage via some
           * sort of sanity check, but this would be brittle and would only
           * catch a small subset of the bad cases... so leaving it up to F* to
           * enforce all of these invariants. *)
          if t = CStar.Void then
            raise_error (BadFrame ("non-empty return, but return type is void"))
      | _ ->
          fatal_error "Internal failure: didn't insert a return"
      end;
      List.tl (List.rev (e :: rest))

  (* Note: block scopes may not fit the entire function body, so it's ok if we
   * have an unmatched pushframe at the beginning (or an unmatched popframe at
   * the end *)

  | stmts, _ ->
      stmts

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
  | TBound _ ->
      fatal_error "Internal failure: no TBound here"
  | TApp (lid, _) ->
      raise_error (ExternalTypeApp lid)
  | TTuple _ ->
      fatal_error "Internal failure: TTuple not desugared here"


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
    CStar.name = ensure_fresh env binder.node.name body;
    typ = translate_type env binder.typ
  } in
  push env binder, binder

and a_unit_is_a_unit binders body =
  (** A function that has a sole unit argument is a C* function with zero
   * arguments. *)
  match binders with
  | [ { typ = TUnit; _ } ] ->
      [], DeBruijn.lift 1 ((object
        inherit DeBruijn.map_counting
        method! ebound i _ j =
          if i = j then
            EUnit
          else
            EBound j
      end) # visit 0 body)
  | _ ->
      binders, body

and translate_declaration env d: CStar.decl option =
  let wrap_throw name (comp: CStar.decl Lazy.t) =
    try Lazy.force comp with
    | Error e ->
        raise_error_l (Warnings.locate name e)
  in

  match d with
  | DFunction (_, t, name, binders, body) ->
      let env = locate env (InTop name) in
      Some (wrap_throw (string_of_lident name) (lazy begin
        let t = translate_return_type env t in
        assert (env.names = []);
        let binders, body = a_unit_is_a_unit binders body in
        let env, binders = translate_and_push_binders env binders in
        let body = translate_function_block env body t in
        CStar.Function (t, (string_of_lident name), binders, body)
      end))

  | DGlobal (_, name, t, body) ->
      let env = locate env (InTop name) in
      Some (CStar.Global (
        string_of_lident name,
        translate_type env t,
        translate_expr env false body))

  | DExternal (name, t) ->
      Some (CStar.External (string_of_lident name, translate_type env t))

  | DType (name, Flat fields) ->
      let name = string_of_lident name in
      (* TODO: avoid collisions since "_s" is not going through the name
       * generator *)
      Some (CStar.Type (
        name, CStar.Struct (None, List.map (fun (field, (typ, _)) ->
          field, translate_type env typ
        ) fields)))

  | DType (name, Abbrev (n, t)) ->
      if n = 0 then
        Some (CStar.Type (string_of_lident name, translate_type env t))
      else
        None

  | DType (_name, Variant _) ->
      failwith "TODO"


and translate_program name decls =
  KList.filter_map (fun d ->
    let n = string_of_lident (PrintAst.decl_name d) in
    try
      translate_declaration empty d
    with Error e -> 
      Warnings.maybe_fatal_error (fst e, Dropping (name ^ "/" ^ n, e));
      None
  ) decls

and translate_file (name, program) =
  name, (translate_program name) program

and translate_files files =
  List.map translate_file files

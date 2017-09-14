(** Translation from Low* to C* *)

(** In order to qualify as a Low* AST (and hence be eligible for translation),
 * the following criteria must be satisfied:
 * - no nested let-bindings;
 * - no matches (at the moment);
 * - in the body of let-bindings, the test expression of conditionals, the
 *   right-hand side of assignments, in all buffer expressions, in function
 *   arguments the following are disallowed:
 *   - sequence expressions
 *   - conditionals
 *   - assignments
 *   - buffer writes
 *   - let-bindings
 *   - impure function calls
 * - the first subexpression of buffer reads, writes and subs must be a
 *   qualified or local name.
 *)

open Ast
open Idents
open Warnings
open Location
open PrintAst.Ops
open Helpers

module C = Checker

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
  This is caught by the second (List.exists ...) test.

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

  ML: shadowing within your own block after conversion to a C identifier
    let x_ = ... in
    let x' = ... in
    ... x_ ...
  InternalAST (DeBruijn):
    let x = ... in
    let x = ... in
    ... @1 ...
  C:
    int x = ...;
    int x1 = ... x ...;
  This is caught by the visitor that visits the continuation of the let-binding.
  Since I'm not opening binders, the reference 0 must be skipped (it's the
  binding we're working) and since the binder has not been pushed into the
  environment yet, we must shift by 1.

  The continuation is a list for cases where the scope of the binder spans
  multiple expressions (e.g. for loop).
*)
let ensure_fresh env name body cont =
  let tricky_shadowing_see_comment_above name body k =
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
            if i - k >= 0 then
              r := !r || name = List.nth env (i - k);
            EBound i
        end) # visit env.names body);
        !r
  in
  mk_fresh name (fun tentative ->
    tricky_shadowing_see_comment_above tentative body 0 ||
    List.exists (fun cont -> tricky_shadowing_see_comment_above tentative (Some cont) 1) cont ||
    List.exists ((=) tentative) env.in_block)


(** AstToCStar performs a unit-to-void conversion.
 *
 * Functions that TAKE a single unit argument are translated as functions that
 * take zero arguments. If the argument is a EUnit expression, we drop it;
 * otherwise, we use a comma operator to make sure we don't discard the
 * (potential) side effect of the argument, EVEN THOUGH F* guarantees that an
 * effectful argument is hoisted (see [mk_expr]).
 *
 * Function that RETURN a single unit argument are translated as functions that
 * return void; this means that any [EReturn e] where [e] has type unit becomes
 * a [Return None]. If [e] is not a value, we can use a sequence (see
 * [mk_expr] again). If a function that has undergone unit to void
 * conversion appears in an expression, again, a comma expression comes to the
 * rescue.
 *
 * The translation of function types is aware of this, too.
 *)

let small s = CStar.Constant (K.UInt8, s)
let zero = small "0"

let rec mk_expr env in_stmt e =
  let mk_expr env e = mk_expr env false e in
  match e.node with
  | EBound var ->
      CStar.Var (find env var)
  | EEnum lident ->
      CStar.Qualified (string_of_lident lident)
  | EQualified lident ->
      CStar.Qualified (string_of_lident lident)
  | EConstant c ->
      CStar.Constant c
  | EApp (e, es) ->
      (* Functions that only take a unit take no argument. *)
      let t, ts = flatten_arrow e.typ in
      let call = match ts, es with
        | [ TUnit ], [ { node = EUnit; _ } ] ->
            CStar.Call (mk_expr env e, [])
        | [ TUnit ], [ e' ] ->
            if is_value e' then
              CStar.Call (mk_expr env e, [])
            else
              CStar.Comma (mk_expr env e', CStar.Call (mk_expr env e, []))
        | _ ->
            CStar.Call (mk_expr env e, List.map (mk_expr env) es)
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
  | EBufCreate (l, e1, e2) ->
      CStar.BufCreate (l, mk_expr env e1, mk_expr env e2)
  | EBufCreateL (l, es) ->
      CStar.BufCreateL (l, List.map (mk_expr env) es)
  | EBufRead (e1, e2) ->
      CStar.BufRead (mk_expr env e1, mk_expr env e2)
  | EBufSub (e1, e2) ->
      CStar.BufSub (mk_expr env e1, mk_expr env e2)
  | EOp (o, w) ->
      CStar.Op (o, w)
  | ECast (e, t) ->
      CStar.Cast (mk_expr env e, mk_type env t)
  | EAbort s ->
      CStar.EAbort (mk_type env e.typ, Option.or_empty s)
  | EUnit ->
      CStar.Cast (zero, CStar.Pointer CStar.Void)
  | EAny ->
      CStar.Any
  | EBool b ->
      CStar.Bool b
  | EString s ->
      CStar.StringLiteral s
  | EFlat fields ->
      let name = match e.typ with TQualified lid -> Some (string_of_lident lid) | _ -> None in
      CStar.Struct (name, List.map (fun (name, expr) ->
        name, mk_expr env expr
      ) fields)
  | EField (expr, field) ->
      CStar.Field (mk_expr env expr, field)

  | EComment (s, e, s') ->
      CStar.InlineComment (s, mk_expr env e, s')

  | EAddrOf e ->
      CStar.AddrOf (mk_expr env e)

  | _ ->
      Warnings.maybe_fatal_error ("", NotLowStar e);
      CStar.Any

and mk_buf env t =
  match t with
  | TBuf t1 | TArray (t1, _) ->
      mk_type env t1
  | _ ->
      invalid_arg "mk_buf"

and mk_ignored_stmt env e =
  if is_value e then
    env, []
  else
    let e = strip_cast e in
    let s =
      match e.typ with
      | TUnit ->
          CStar.Ignore (mk_expr env true e)
      | _ ->
          CStar.Ignore (CStar.Cast (mk_expr env true e, CStar.Void))
    in
    env, [s]

and mk_stmts env e ret_type =
  let rec collect (env, acc) return_pos e =
    match e.node with
    | ELet (binder, e1, e2) ->
        let env, binder = mk_and_push_binder env binder (Some e1) [ e2 ]
        and e1 = mk_expr env false e1 in
        let acc = CStar.Decl (binder, e1) :: acc in
        collect (env, acc) return_pos e2

    | EWhile (e1, e2) ->
        let e = CStar.While (mk_expr env false e1, mk_block env false e2) in
        env, e :: acc

    | EFor (_,
      { node = EConstant (K.UInt32, init); _ },
      { node = EApp (
        { node = EOp (K.Lt, K.UInt32); _ },
        [{ node = EBound 0; _ };
        { node = EConstant (K.UInt32, max); _ }]); _},
      { node = EAssign (
        { node = EBound 0; _ },
        { node = EApp (
          { node = EOp (K.Add, K.UInt32); _ },
          [{ node = EBound 0; _ };
          { node = EConstant (K.UInt32, incr); _ }]); _}); _},
      body)
      when (
        let init = int_of_string init in
        let max = int_of_string max in
        let incr = int_of_string incr in
        let len = (max - init) / incr in
        len <= !Options.unroll_loops
      )
      ->
        let init = int_of_string init in
        let max = int_of_string max in
        let incr = int_of_string incr in
        let rec mk acc i =
          if i < max then
            let body = DeBruijn.subst (mk_uint32 i) 0 body in
            mk (CStar.Block (mk_block env false body) :: acc) (i + incr)
          else
            acc
        in
        env, mk [] init @ acc


    | EFor (binder, e1, e2, e3, e4) ->
        (* Note: the arguments to mk_and_push_binder are solely for the purpose
         * of avoiding name collisions. *)
        let is_solo_assignment = binder.node.meta = Some MetaSequence in
        let env', binder = mk_and_push_binder env binder (Some e1) [ e2; e3; e4 ] in
        let e2 = mk_expr env' false e2 in
        let e3 = KList.one (mk_block env' false e3) in
        let e4 = mk_block env' false e4 in
        let e =
          if is_solo_assignment then
            let _ = KPrint.bprintf "e1 is %a\n" pexpr e1 in
            let e1 = KList.one (mk_block env false e1) in
            CStar.For (`Stmt e1, e2, e3, e4)
          else
            let e1 = mk_expr env false e1 in
            CStar.For (`Decl (binder, e1), e2, e3, e4)
        in
        env', e :: acc

    | EIfThenElse (e1, e2, e3) ->
        let e = CStar.IfThenElse (mk_expr env false e1, mk_block env return_pos e2, mk_block env return_pos e3) in
        env, e :: acc

    | ESequence es ->
        let n = List.length es in
        KList.fold_lefti (fun i (_, acc) e ->
          let return_pos = i = n - 1 && return_pos in
          collect (env, acc) return_pos e
        ) (env, acc) es

    | EAssign (e1, ({ node = (EBufCreate _ | EBufCreateL _); _ } as e2)) when is_array e1.typ ->
        let e = CStar.Copy (mk_expr env false e1, mk_type env e1.typ, mk_expr env false e2) in
        env, e :: acc

    | EAssign (e1, e2) ->
        let e = CStar.Assign (mk_expr env false e1, mk_expr env false e2) in
        env, e :: acc

    | EBufBlit (e1, e2, e3, e4, e5) ->
        let e = CStar.BufBlit (
          mk_expr env false e1,
          mk_expr env false e2,
          mk_expr env false e3,
          mk_expr env false e4,
          mk_expr env false e5
        ) in
        env, e :: acc

    | EBufWrite (e1, e2, e3) ->
        let e = CStar.BufWrite (
          mk_expr env false e1,
          mk_expr env false e2,
          mk_expr env false e3
        ) in
        env, e :: acc

    | EBufFill (e1, e2, e3) ->
        let e = CStar.BufFill (
          mk_expr env false e1,
          mk_expr env false e2,
          mk_expr env false e3
        ) in
        env, e :: acc

    | EMatch _ ->
        fatal_error "[AstToCStar.collect EMatch]: not implemented"

    | EPushFrame ->
        env, CStar.PushFrame :: acc

    | EPopFrame ->
        env, CStar.PopFrame :: acc

    | EAbort s ->
        env, CStar.Abort (Option.or_empty s) :: acc

    | ESwitch (e, branches) ->
        env, CStar.Switch (mk_expr env false e,
          List.map (fun (lid, e) ->
            string_of_lident lid, mk_block env return_pos e
          ) branches) :: acc

    | EReturn e ->
        mk_as_return env e acc return_pos

    | EComment (s, e, s') ->
        let env, stmts = collect (env, CStar.Comment s :: acc) return_pos e in
        env, CStar.Comment s' :: stmts

    | EIgnore e ->
        let env, s = mk_ignored_stmt env e in
        env, s @ acc

    | _ when return_pos ->
        mk_as_return env e acc return_pos

    | _ ->
        if is_value e then
          env, acc
        else
          let e = CStar.Ignore (mk_expr env true e) in
          env, e :: acc

  and mk_block env return_pos e =
    List.rev (snd (collect (reset_block env, []) return_pos e))

  and mk_as_return env e acc return_pos =
    let maybe_return_nothing s =
      (* "return" when already in return position is un-needed *)
      if return_pos then s else CStar.Return None :: s
    in
    if ret_type = CStar.Void && is_value e then
      env, maybe_return_nothing acc
    else if ret_type = CStar.Void then
      let env, s = mk_ignored_stmt env e in
      env, maybe_return_nothing (s @ acc)
    else
      env, CStar.Return (Some (mk_expr env false e)) :: acc

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
and mk_function_block env e t =
  (** This function expects an environment where names and in_block have been
   * populated with the function's parameters. *)
  let stmts = mk_stmts env e t in

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
      (* Note: it is no longer the case that [e] ought to be a [Return]. It
       * could be, for instance, an if-then-else with several [Returns] in
       * terminal position. [Simplify.fixup_return_pos] is precisely about this. *)
      List.tl (List.rev (e :: rest))

  (* Note: block scopes may not fit the entire function body, so it's ok if we
   * have an unmatched pushframe at the beginning (or an unmatched popframe at
   * the end *)

  | stmts, _ ->
      stmts

and mk_return_type env = function
  | TInt w ->
      CStar.Int w
  | TArray (t, k) ->
      CStar.Array (mk_type env t, CStar.Constant k)
  | TBuf t ->
      CStar.Pointer (mk_type env t)
  | TUnit ->
      CStar.Void
  | TQualified name ->
      CStar.Qualified (string_of_lident name)
  | TBool ->
      CStar.Bool
  | TAny ->
      CStar.Pointer CStar.Void
  | TArrow _ as t ->
      let ret, args = flatten_arrow t in
      CStar.Function (None, mk_return_type env ret, List.map (mk_type env) args)
  | TZ ->
      CStar.Z
  | TBound _ ->
      fatal_error "Internal failure: no TBound here"
  | TApp (lid, _) ->
      raise_error (ExternalTypeApp lid)
  | TTuple _ ->
      fatal_error "Internal failure: TTuple not desugared here"
  | TAnonymous t ->
      mk_type_def env t


and mk_type env = function
  | TUnit ->
      CStar.Pointer CStar.Void
  | t ->
      mk_return_type env t

(* This one is used for function binders, which we assume are distinct from each
 * other. *)
and mk_and_push_binders env binders =
  let env, acc = List.fold_left (fun (env, acc) binder ->
    let env, binder = mk_and_push_binder env binder None [] in
    env, binder :: acc
  ) (env, []) binders in
  env, List.rev acc

and mk_and_push_binder env binder body cont =
  let binder = {
    CStar.name = ensure_fresh env binder.node.name body cont;
    typ = mk_type env binder.typ
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

and mk_declaration env d: CStar.decl option =
  let wrap_throw name (comp: CStar.decl Lazy.t) =
    try Lazy.force comp with
    | Error e ->
        raise_error_l (Warnings.locate name e)
    | e ->
        KPrint.beprintf "Error in: %s\n" name;
        raise e
  in

  match d with
  | DFunction (cc, flags, n, t, name, binders, body) ->
      assert (n = 0);
      let env = locate env (InTop name) in
      Some (wrap_throw (string_of_lident name) (lazy begin
        let t = mk_return_type env t in
        assert (env.names = []);
        let binders, body = a_unit_is_a_unit binders body in
        let env, binders = mk_and_push_binders env binders in
        let body = mk_function_block env body t in
        CStar.Function (cc, flags, t, (string_of_lident name), binders, body)
      end))

  | DGlobal (flags, name, t, body) ->
      let env = locate env (InTop name) in
      Some (CStar.Global (
        string_of_lident name,
        flags,
        mk_type env t,
        mk_expr env false body))

  | DExternal (cc, name, t) ->
      let to_void = match t with
        | TArrow (TUnit, _) -> true
        | _ -> false
      in
      let open CStar in
      let t = match mk_type env t with
        | Function (None, ret, args) ->
            let args = match args with
              | [ Pointer Void ] when to_void -> []
              | _ -> args
            in
            Function (cc, ret, args)
        | Function (Some _, _, _) ->
            failwith "impossible"
        | t ->
            assert (cc = None);
            t
      in
      Some (External (string_of_lident name, t))

  | DType (name, 0, def) ->
      let name = string_of_lident name in
      Some (CStar.Type (name, mk_type_def env def))

  | DType _ ->
      None

and mk_type_def env d: CStar.typ =
  match d with
  | Flat fields ->
      (* Not naming the structs or enums here, because they're going to be
       * typedef'd and we'll only refer to the typedef'd name. *)
      CStar.Struct (List.map (fun (field, (typ, _)) ->
        field, mk_type env typ
      ) fields)

  | Abbrev t ->
      mk_type env t

  | Variant _ ->
      failwith "Variant should've been desugared at this stage"

  | Enum tags ->
      CStar.Enum (List.map string_of_lident tags)

  | Union fields ->
      CStar.Union (List.map (fun (f, t) ->
        f, mk_type env t
      ) fields)


and mk_program name decls =
  KList.filter_map (fun d ->
    let n = string_of_lident (Ast.lid_of_decl d) in
    try
      mk_declaration empty d
    with
    | Error e ->
        Warnings.maybe_fatal_error (fst e, Dropping (name ^ "/" ^ n, e));
        None
    | e ->
        Warnings.fatal_error "Fatal failure in %a: %s\n"
          plid (Ast.lid_of_decl d)
          (Printexc.to_string e)
  ) decls

and mk_file (name, program) =
  name, (mk_program name) program

and mk_files files =
  List.map mk_file files

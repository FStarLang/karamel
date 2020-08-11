(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 License. *)

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
open Warn
open Loc
open PrintAst.Ops
open Helpers

module C = Checker
module LidSet = Idents.LidSet

type env = {
  location: loc list;
  names: ident list;
  type_names: ident list;
    (* type names which we never can shadow via a local, see NameCollision.test *)
  in_block: ident list;
  ifdefs: LidSet.t;
  macros: LidSet.t;
}

let locate env loc =
  { env with location = update_location env.location loc }

let empty: env = {
  names = [];
  type_names = [];
  in_block = [];
  location = [];
  ifdefs = LidSet.empty;
  macros = LidSet.empty;
}

let reset_block env = {
  env with in_block = []
}

let push env binder = CStar.{
  type_names = env.type_names;
  names = binder.name :: env.names;
  in_block = binder.name :: env.in_block;
  location = env.location;
  ifdefs = env.ifdefs;
  macros = env.macros
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
        (object
          inherit [_] iter
          method! extend env binder =
            binder.node.name :: env
          method! visit_EBound (env, _) i =
            if i - k >= 0 then
              r := !r || name = List.nth env (i - k);
        end)#visit_expr_w env.names body;
        !r
  in
  mk_fresh name (fun tentative ->
    tricky_shadowing_see_comment_above tentative body 0 ||
    List.exists (fun cont -> tricky_shadowing_see_comment_above tentative (Some cont) 1) cont ||
    List.mem tentative env.in_block ||
    !Options.no_shadow && List.mem tentative env.names ||
    List.mem tentative env.type_names)


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

exception NotIfDef

(** Treatment of return position. We either:
  * - not in a return position
  * - in a position where we may choose to insert a return (or skip it, e.g. if
  *   the function returns void and we're in terminal position already)
  * - in a position where we must early-return. *)
type return_pos =
  | Not
  | May
  | Must

type binder_pos = Function | Local

let string_of_return_pos = function
  | Not -> "Not"
  | May -> "May"
  | Must -> "Must"

let rec mk_expr env in_stmt e =
  let mk_expr env e = mk_expr env false e in
  match e.node with
  | EBound var ->
      CStar.Var (find env var)
  | EEnum lident ->
      CStar.Qualified lident
  | EQualified lident ->
      if LidSet.mem lident env.ifdefs then
        Warn.(maybe_fatal_error (KPrint.bsprintf "%a" Loc.ploc env.location, IfDef lident));
      if LidSet.mem lident env.macros then
        CStar.Macro lident
      else
        CStar.Qualified lident
  | EConstant c ->
      CStar.Constant c
  | EApp (e, es) ->
      (* Functions that only take a unit take no argument. *)
      let t, ts = flatten_arrow e.typ in
      let call = match ts, es with
        | [ TUnit ], [ { node = EUnit; _ } ] ->
            CStar.Call (mk_expr env e, [])
        | [ TUnit ], [ e' ] ->
            if is_readonly_c_expression e' then
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
      let name = match e.typ with TQualified lid -> Some lid | _ -> None in
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
      Warn.maybe_fatal_error (KPrint.bsprintf "%a" Loc.ploc env.location, NotLowStar e);
      CStar.Any

and mk_ignored_stmt env e =
  if is_readonly_c_expression e then
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
  let rec collect (env, acc) (return_pos: return_pos) e =
    (* If we reach the end of the list of statements and are at a terminal atomic
     * node (not a disjunction in the control-flow), we may be required when `ret_type
     * = Must` to insert a return. *)
    let maybe_return acc =
      if return_pos = Must then
        CStar.Return None :: acc
      else
        acc
    in

    match e.node with
    | ELet (binder, e1, e2) ->
        let env, binder = mk_and_push_binder env binder Local (Some e1) [ e2 ]
        and e1 = mk_expr env false e1 in
        let acc = CStar.Decl (binder, e1) :: acc in
        collect (env, acc) return_pos e2

    | EWhile (e1, e2) ->
        let e = CStar.While (mk_expr env false e1, mk_block env Not e2) in
        env, maybe_return (e :: acc)

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
            mk (CStar.Block (mk_block env Not body) :: acc) (i + incr)
          else
            acc
        in
        env, maybe_return (mk [] init @ acc)


    | EFor (binder, e1, e2, e3, e4) ->
        (* Note: the arguments to mk_and_push_binder are solely for the purpose
         * of avoiding name collisions. *)
        let is_solo_assignment = binder.node.meta = Some MetaSequence in
        let env', binder = mk_and_push_binder env binder Local (Some e1) [ e2; e3; e4 ] in
        let e2 = mk_expr env' false e2 in
        let e3 = KList.last (mk_block env' Not e3) in
        let e4 = mk_block env' Not e4 in
        let e =
          if is_solo_assignment then
            let e1 = match mk_block env Not e1 with
              | [ e1 ] -> `Stmt e1
              | [] -> `Skip
              | _ -> assert false
            in
            CStar.For (e1, e2, e3, e4)
          else
            let e1 = mk_expr env false e1 in
            CStar.For (`Decl (binder, e1), e2, e3, e4)
        in
        env', maybe_return (e :: acc)

    | EIfThenElse (e1, e2, e3) ->
        begin try
          env, mk_ifdef env return_pos acc e1 e2 e3
        with NotIfDef ->
          (* Early return optimization. It is sometimes more idiomatic in C to write:
           *
           * if (...) {
           *   ...;
           *   return ...;
           * }
           * ...
           *
           * than
           *
           * if (...) {
           *   ...;
           *   return ...;
           * } else {
           *   ...
           * }
           *)
          if not !Options.no_return_else || return_pos = Not then
            (* No optimization *)
            let e = CStar.IfThenElse (false,
              mk_expr env false e1,
              mk_block env return_pos e2,
              mk_block env return_pos e3
            ) in
            env, e :: acc
          else
            (* no_return_else && return_pos <> Not,
             *   i.e. optimization enabled; we are in return position *)
            let e = CStar.IfThenElse (false,
              mk_expr env false e1,
              mk_block env Must e2,
              []
            ) in
            collect (env, e :: acc) return_pos e3
        end

    | ESequence es ->
        let n = List.length es in
        KList.fold_lefti (fun i (_, acc) e ->
          let return_pos = if i = n - 1 then return_pos else Not in
          collect (env, acc) return_pos e
        ) (env, acc) es

    | EAssign (e1, _) when is_array e1.typ ->
        assert false

    | EAssign (e1, e2) ->
        let e = CStar.Assign (mk_expr env false e1, mk_type env e1.typ, mk_expr env false e2) in
        env, maybe_return (e :: acc)

    | EBufBlit (e1, e2, e3, e4, e5) ->
        let e = CStar.BufBlit (
          mk_type env (assert_tbuf e1.typ),
          mk_expr env false e1,
          mk_expr env false e2,
          mk_expr env false e3,
          mk_expr env false e4,
          mk_expr env false e5
        ) in
        env, maybe_return (e :: acc)

    | EBufWrite (e1, e2, e3) ->
        let e = CStar.BufWrite (
          mk_expr env false e1,
          mk_expr env false e2,
          mk_expr env false e3
        ) in
        env, maybe_return (e :: acc)

    | EBufFill (e1, e2, e3) ->
        let e = CStar.BufFill (
          mk_type env (assert_tbuf e1.typ),
          mk_expr env false e1,
          mk_expr env false e2,
          mk_expr env false e3
        ) in
        env, maybe_return (e :: acc)

    | EBufFree e ->
        let e = CStar.BufFree (mk_expr env false e) in
        env, maybe_return (e :: acc)

    | EMatch _ ->
        fatal_error "[AstToCStar.collect EMatch]: not implemented"

    | EAbort s ->
        env, CStar.Abort (Option.or_empty s) :: acc

    | ESwitch (e, branches) ->
        let default, branches =
          List.partition (function (SWild, _) -> true | _ -> false) branches
        in
        let default = match default with
          | [ SWild, e ] -> Some (mk_block env return_pos e)
          | [] -> None
          | _ -> failwith "impossible"
        in
        env, CStar.Switch (mk_expr env false e,
          List.map (fun (lid, e) ->
            (match lid with
            | SConstant k -> `Int k
            | SEnum lid -> `Ident lid
            | _ -> failwith "impossible"),
            mk_block env return_pos e
          ) branches, default) :: acc

    | EReturn e ->
        mk_as_return env e acc Must

    | EComment (s, e, s') ->
        let env, stmts = collect (env, CStar.Comment s :: acc) return_pos e in
        env, CStar.Comment s' :: stmts

    | EStandaloneComment s ->
        env, maybe_return (CStar.Comment s :: acc)

    | EIgnore e ->
        let env, s = mk_ignored_stmt env e in
        env, maybe_return (s @ acc)

    | EBreak ->
        env, CStar.Break :: acc

    | EPushFrame ->
        env, acc

    | _ when return_pos <> Not ->
        mk_as_return env e acc return_pos

    | _ ->
        (* This is a specialized instance of `mk_as_return` when return_pos = Not *)
        if is_readonly_c_expression e then
          env, acc
        else
          let e = CStar.Ignore (mk_expr env true e) in
          env, e :: acc

  and mk_block env return_pos e =
    List.rev (snd (collect (reset_block env, []) return_pos e))

  and mk_as_return env e acc return_pos =
    let maybe_return_nothing s =
      (* "return" when already in return position is un-needed *)
      if return_pos = May then s else CStar.Return None :: s
    in
    if ret_type = CStar.Void && is_readonly_c_expression e then
      env, maybe_return_nothing acc
    else if ret_type = CStar.Void then
      let env, s = mk_ignored_stmt env e in
      env, maybe_return_nothing (s @ acc)
    else
      env, CStar.Return (Some (mk_expr env false e)) :: acc

  and mk_ifdef env return_pos acc e1 e2 e3 =
    try
      (* First compilation scheme: a cascading chain of if-then-else. *)
      let cond = mk_ifcond env e1 in
      CStar.IfThenElse (true,
        cond,
        mk_block env return_pos e2,
        mk_elif env return_pos e3
      ) :: acc
    with NotIfDef ->
      (* Second compilation scheme: fall-through (terminal position).
       *
       * if B1 && b2 then
       *   e2
       * else
       *   e3
       *
       * becomes:
       *
       * if B1 then
       *   if b2 then
       *     return e2
       * return e3
       *
       * TODO: make this a little smarter, e.g. if the conjunction is
       * ill-parenthesized, or if there's B1 && B'1
       *)
      match e1.node with
      | EApp ({ node = EOp (K.And, K.Bool); _ }, [ e1; e1' ]) when return_pos <> Not ->
          let cond = mk_ifcond env e1 in
          (* Can't recursively call mk_block with Must because it'll insert a
           * return in the else-branch. *)
          let e2 = Helpers.nest_in_return_pos TUnit (fun _ e -> with_type TUnit (EReturn e)) e2 in
          let inner_if = mk_block env Not (with_unit (EIfThenElse (e1', e2, eunit))) in
          let acc = CStar.IfThenElse (true, cond, inner_if, []) :: acc in
          snd (collect (env, acc) return_pos e3)
      | _ ->
          raise NotIfDef

  and mk_elif env return_pos e3 =
    match e3.node with
    | EIfThenElse (e1', e2', e3') ->
        begin try
          let cond = mk_ifcond env e1' in
          [ CStar.IfThenElse (
              true, cond, mk_block env return_pos e2', mk_elif env return_pos e3')]
        with NotIfDef ->
          mk_block env return_pos e3
        end
    | _ ->
        mk_block env return_pos e3

  and mk_ifcond env e =
    match e.node with
    | EQualified name when LidSet.mem name env.ifdefs ->
        CStar.Macro name
    | EApp ({ node = EOp ((K.And | K.Or) as o, K.Bool); _ }, [ e1; e2 ]) ->
        CStar.Call (CStar.Op (o, K.Bool), [ mk_ifcond env e1; mk_ifcond env e2 ])
    | _ ->
        raise NotIfDef

  in

  snd (collect (env, []) May e)


and mk_function_block env e t =
  List.rev (mk_stmts env e t)

(* These two mutually recursive functions implement a unit-to-void type translation that is
 * consistent with the same translation for expressions above. *)
and mk_return_type env = function
  | TInt w ->
      CStar.Int w
  | TArray (t, k) ->
      CStar.Array (mk_type env t, CStar.Constant k)
  | TBuf (t, true) ->
      CStar.(Pointer (Const (mk_type env t)))
  | TBuf (t, false) ->
      CStar.Pointer (mk_type env t)
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
      let args = match args with [ TUnit ] -> [] | _ -> args in
      CStar.Function (None, mk_return_type env ret, List.map (mk_type env) args)
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
    let env, binder = mk_and_push_binder env binder Function None [] in
    env, binder :: acc
  ) (env, []) binders in
  env, List.rev acc

and mk_and_push_binder env binder pos body cont =
  let name =
    if !Options.microsoft then
      match pos with
      | Local -> GlobalNames.camel_case binder.node.name
      | Function -> GlobalNames.pascal_case binder.node.name
    else
      binder.node.name
  in
  let binder = {
    CStar.name = ensure_fresh env name body cont;
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
        method! visit_EBound (i, _) j =
          if i = j then
            EUnit
          else
            EBound j
      end)#visit_expr_w 0 body)
  | _ ->
      binders, body

and mark_const has_const t =
  if has_const then
    match t with
    | CStar.Pointer t ->
        CStar.Pointer (mark_const true t)
    | _ ->
        CStar.Const t
  else
    t

and mark_binders_const flags binders =
  List.map (fun { CStar.name; typ } ->
    { CStar.name; typ = mark_const (List.mem (Common.Const name) flags) typ }
  ) binders

and mk_declaration m env d: (CStar.decl * _) option =
  let wrap_throw name (comp: CStar.decl Lazy.t) =
    try Lazy.force comp with
    | Error e ->
        raise_error_l (Warn.locate name e)
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
        let binders, body = a_unit_is_a_unit binders body in
        let env, binders = mk_and_push_binders env binders in
        let binders = mark_binders_const flags binders in
        let body = mk_function_block env body t in
        CStar.Function (cc, flags, t, name, binders, body)
      end), [])

  | DGlobal (flags, name, n, t, body) ->
      assert (n = 0);
      let env = locate env (InTop name) in
      let macro = LidSet.mem name env.macros in
      Some (CStar.Global (
        name,
        macro,
        flags,
        mk_type env t,
        mk_expr env false body), [])

  | DExternal (cc, flags, name, t, pp) ->
      if LidSet.mem name env.ifdefs then
        None
      else
        let add_cc = function
          | CStar.Function (_, t, ts) -> CStar.Function (cc, t, ts)
          | t -> t
        in
        Some (CStar.External (name, add_cc (mk_type env t), flags, pp), [])

  | DType (name, flags, _, Forward) ->
      Some (CStar.TypeForward (name, flags), [ GlobalNames.to_c_name m name ])

  | DType (name, flags, 0, def) ->
      Some (CStar.Type (name, mk_type_def env def, flags), [ GlobalNames.to_c_name m name ] )

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
      CStar.Enum tags

  | Union fields ->
      CStar.Union (List.map (fun (f, t) ->
        f, mk_type env t
      ) fields)

  | Forward ->
      failwith "impossible, handled by mk_declaration"


and mk_program m name env decls =
  let decls, _ = List.fold_left (fun (decls, names) d ->
    let n = string_of_lident (Ast.lid_of_decl d) in
    match mk_declaration m { env with type_names = names } d with
    | exception (Error e) ->
        Warn.maybe_fatal_error (fst e, Dropping (name ^ "/" ^ n, e));
        decls, names
    | exception e ->
        Warn.fatal_error "Fatal failure in %a: %s\n"
          plid (Ast.lid_of_decl d)
          (Printexc.to_string e)
    | None ->
        decls, names
    | Some (decl, name) ->
        decl :: decls, name @ names
  ) ([], []) decls in
  List.rev decls

and mk_files files file_of m ifdefs macros =
  let env = { empty with ifdefs; macros } in
  List.map (fun file ->
    let deps = 
      Hashtbl.fold (fun k _ acc -> k :: acc) (Bundles.direct_dependencies file_of file) []
    in
    let name, program = file in
    name, deps, mk_program m name env program
  ) files

let mk_macros_set files =
  (object
    inherit [_] reduce
    method private zero = LidSet.empty
    method private plus = LidSet.union
    method visit_DGlobal _ flags name _ _ body =
      if List.mem Common.Macro flags then
        if body.node = EAny then begin
          Warn.(maybe_fatal_error ("", CannotMacro name));
          LidSet.empty
        end else
          LidSet.singleton name
      else
        LidSet.empty
  end)#visit_files () files

let mk_ifdefs_set files =
  (object
    inherit [_] reduce
    method private zero = LidSet.empty
    method private plus = LidSet.union
    method visit_DExternal _ _ flags name _ _ =
      if List.mem Common.IfDef flags then
        LidSet.singleton name
      else
        LidSet.empty
  end)#visit_files () files

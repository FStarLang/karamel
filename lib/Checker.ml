(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 and MIT Licenses. *)

(** Checking the well-formedness of a program in [Ast] *)

(** TODO this module needs to be rewritten properly with constraints and
 * everything; the bidirectional algorithm is remarkably poor and extremely
 * fragile! *)

open Ast
open Constant
open Loc
open PrintAst.Ops
open Helpers

let buf_any_msg = format_of_string {|
This subexpression creates a buffer with an unknown type:
  %a

Here's a hint. If you're using untagged unions, instead of:

  match e with
  | Foo ->
      Buffer.create e1 l1
  | Bar ->
      Buffer.create e2 l2

where e1: t1 and e2: t2, try:

  match e with
  | Foo ->
      let b: Buffer.buffer t1 = Buffer.create e1 l1 in
      b
  | Bar ->
      let b: Buffer.buffer t2 = Buffer.create e2 l2 in
      b
|}

(** Environments ------------------------------------------------------------ *)

module M = Map.Make(struct
  type t = lident
  let compare = compare
end)

let uint32 = TInt UInt32
let sizet = TInt SizeT
let c_string = TQualified ([ "Prims" ], "string")

type env = {
  globals: typ M.t;
  locals: binder list;
  types: type_def M.t;
  location: loc list;
  enums: lident M.t;
  warn: bool;
  n_cgs: int;
    (* Number of const generics, useful only for type-checking stuff coming in from Eurydice pre-monomorphization. *)
}

let empty: env = {
  globals = M.empty;
  locals = [];
  types = M.empty;
  location = [];
  enums = M.empty;
  warn = false;
  n_cgs = 0
}

let push env binder =
  (* KPrint.bprintf "pushing %s at type %a\n" binder.node.name ptyp binder.typ; *)
  { env with locals = binder :: env.locals }

let find env i =
  List.nth env.locals i

(** Errors ------------------------------------------------------------------ *)

(* An error for which the only way to recover is to drop the definition. *)
exception CheckerError of Error.t

let checker_error env fmt =
  Printf.kbprintf (fun buf ->
    raise (CheckerError (KPrint.bsprintf "%a" ploc env.location, Error.TypeError (Buffer.contents buf)))
  ) (Buffer.create 16) fmt

let check_mut env s c =
  if c then
    checker_error env "%s requires a non-const pointer" s

(** Environments, continued ------------------------------------------------- *)

let lookup_type env lid =
  match M.find lid env.types with
  | exception Not_found ->
      checker_error env "Reference to undefined type: %a" plid lid
  | x ->
      x

let lookup_global env lid =
  match M.find lid env.globals with
  | exception Not_found ->
      if env.warn then
        Warn.(maybe_fatal_error (KPrint.bsprintf "%a" ploc env.location,
          UnboundReference (KPrint.bsprintf "%a" plid lid)));
      TAny
  | x ->
      x

let populate_env files =
  List.fold_left (fun env (_, decls) ->
    List.fold_left (fun env decl ->
      match decl with
      | DType (lid, _, _, _, typ) ->
          let env = match typ with
          | Enum tags ->
              List.fold_left (fun env (tag, _) ->
                { env with enums = M.add tag lid env.enums }
              ) env tags
          | _ ->
              env
          in
          { env with types = M.add lid typ env.types }
      | DGlobal (_, lid, n, t, _) ->
          assert (n = 0);
          { env with globals = M.add lid t env.globals }
      | DFunction (_, _, n_cgs, n, ret, lid, binders, _) ->
          if not !Options.allow_tapps && n <> 0 then
            Warn.fatal_error "%a is polymorphic\n" plid lid;
          let t = List.fold_right (fun b t2 -> TArrow (b.typ, t2)) binders ret in
          let t = if n_cgs > 0 || n > 0 then TPoly ({ n; n_cgs }, t) else t in
          { env with globals = M.add lid t env.globals }
      | DExternal (_, _, _, _, lid, typ, _) ->
          { env with globals = M.add lid typ env.globals }
    ) env decls
  ) empty files

let known_type env lid =
  M.mem lid env.types

let locate env loc =
  { env with location = update_location env.location loc }

(** Checking ---------------------------------------------------------------- *)

type flat = Record | Union

let kind env lid: flat option =
  match lookup_type env lid with
  | Flat _ -> Some Record
  | Union _ -> Some Union
  | _ -> None


let rec check_everything ?warn files: bool * file list =
  let env = populate_env files in
  let env = match warn with Some true -> { env with warn = true } | _ -> env in
  let r = ref false in
  !r, List.map (check_program env r) files

and check_program env r (name, decls) =
  let env = locate env (File name) in
  let by_lid = Hashtbl.create 41 in
  let total = List.length decls in
  let decls = KList.filter_mapi (fun i d ->
    if Options.debug "checker" then
      KPrint.bprintf "CHECKER PROGRESS: %d/%d\n" (i + 1) total;
    try
      check_decl env d;
      Some d
    with
    | CheckerError e ->
        r := true;
        flush stdout;
        if !Options.backtrace then
          Printexc.print_backtrace stderr;
        KPrint.beprintf "Cannot re-check %a as valid Low* and will not extract it.  \
          If %a is not meant to be extracted, consider marking it as Ghost, \
          noextract, or using a bundle. If it is meant to be extracted, use \
          -dast for further debugging.\n\n"
          plid (lid_of_decl d) plid (lid_of_decl d);
        Warn.maybe_fatal_error e;
        KPrint.beprintf "--------------------------------------------------------------------------------\n\n";
        flush stderr;
        None
  ) decls in

  (* Some concise, well-behaved error reporting. *)
  Hashtbl.iter (fun lid decl_lids ->
    let open PPrint in
    let open PrintCommon in
    let mentions = if List.length decl_lids > 1 then string "mention" else string "mentions" in
    KPrint.beprintf "Warning: %a\n" pdoc (
      english_join (List.map print_lident decl_lids) ^/^ mentions ^/^
      print_lident lid ^/^
      flow break1 (words "meaning that they cannot be type-checked by KaRaMeL")
    )
  ) by_lid;

  name, decls


and check_decl env d =
  if Options.debug "checker" then
    KPrint.bprintf "checking %a\n" plid (lid_of_decl d);
  match d with
  | DFunction (_, _, n_cgs, n, t, name, binders, body) ->
      assert (!Options.allow_tapps || n = 0);
      let env = List.fold_left push env binders in
      let env = locate env (InTop name) in
      let env = { env with n_cgs } in
      check env t body
  | DGlobal (_, name, n, t, body) ->
      assert (n = 0);
      let env = locate env (InTop name) in
      check env t body
  | DExternal _
  | DType _ ->
      (* Barring any parameterized types, there's is nothing to check here
       * really. *)
      ()

and check_or_infer env t e =
  if t = TAny then
    infer env e
  else begin
    check env t e;
    t
  end

and smallest t1 t2 =
  (* This barely makes any sense. Need to clean up this typechecking algorithm. *)
  match t1, t2 with
  | TAny, _ ->
      t2
  | _, TAny ->
      t1
  | TBuf (t1, b1), TBuf (t2, b2) ->
      TBuf (smallest t1 t2, b1 && b2)
  | _ ->
      t1

and check_fields_opt env fieldexprs fieldtyps =
  if List.length fieldexprs > List.length fieldtyps then
    checker_error env "some fields are superfluous (expr) in %a" pexpr (with_unit (EFlat fieldexprs));
  List.iter (fun (field, expr) ->
    let field = Option.get field in
    let t, _ = List.assoc (Some field) fieldtyps in
    check env t expr
  ) fieldexprs

and check_fieldpats env fieldexprs fieldtyps =
  if List.length fieldexprs > List.length fieldtyps then
    checker_error env "some fields are superfluous (pat) in %a" ppat (with_unit (PRecord fieldexprs));
  List.iter (fun (field, expr) ->
    let t, _ = List.assoc (Some field) fieldtyps in
    check_pat env t expr
  ) fieldexprs

and check_union env fieldexprs fieldtyps =
  match fieldexprs with
  | [ Some f, e ] ->
      begin try
        check env (List.assoc f fieldtyps) e
      with Not_found ->
        checker_error env "Union does not have such a field"
      end
  | [ None, { node = EConstant (_, "0"); _ } ] ->
      ()
  | _ ->
      checker_error env "Union expected, i.e. exactly one provided field";


and check env t e =
  if Options.debug "checker" then KPrint.bprintf "[check] t=%a for e=%a\n" ptyp t pexpr e;
  if Options.debug "checker" then KPrint.bprintf "[check] annot=%a for e=%a\n" ptyp e.typ pexpr e;
  check' env t e;
  e.typ <- smallest e.typ t

and check' env t e =
  let c t' = check_subtype env t' t in
  match e.node with
  | ETApp (e0, _, _, _) ->
      begin match e0.node with
      | EOp ((K.Eq | K.Neq), _) ->
          (* This is probably old code that predates proper treatment of polymorphic equalities.
             Check if this can be safely removed? *)
          (* Equalities are type checked with Any (??) *)
          check env t e0
      | _ ->
          let t = infer env e in
          assert (t <> TAny);
          (* If it is... probably need to do something like this:
            let t = expand_abbrev env t in
            match flatten_tapp t with
            | exception Invalid_argument _ ->
                assert (cgs' = [] && ts' = []);
                check env t e
            | lid, ts, cgs ->
                List.iter2 (check_subtype env) ts' ts;
                List.iter2 (fun cg cg' ->
                  if cg <> cg' then
                    checker_error env "cg mismatch in tyapp"
                ) cgs cgs';
                check_subtype env (TQualified lid) e
          *)
          c t
      end

  | EPolyComp _
  | EBound _
  | EOpen _
  | EQualified _
  | EConstant _
  | EUnit
  | EAssign _
  | EOp _
  | EPushFrame | EPopFrame
  | EAny | EAbort _
  | EBufNull
  | EReturn _
  | EBreak
  | EContinue
  | EBool _
  | EWhile _
  | EEnum _
  | EField _
  | EString _
  | EFun _
  | EFor _
  | EIgnore _
  | EStandaloneComment _
  | EApp _ ->
      c (infer env e)

  | ECast (_, t) ->
      if t = TAny then
        Warn.maybe_fatal_error ("", NotLowStarCast e);
      c (infer env e)

  | ELet (binder, body, cont) ->
      let t' = check_or_infer (locate env (In binder.node.name)) binder.typ body in
      binder.typ <- t';
      let env = push env binder in
      check (locate env (After binder.node.name)) t cont

  | EIfThenElse (e1, e2, e3) ->
      check env TBool e1;
      check (locate env Then) t e2;
      check (locate env Else) t e3

  | ESequence es ->
      begin match List.rev es with
      | last :: rest ->
          List.iteri (fun i e -> check (locate env (Sequence i)) TUnit e) (List.rev rest);
          check (locate env SequenceLast) t last
      | [] ->
          ()
      end

  | EBufCreate (lifetime, e1, e2) ->
      (* "If the size is an integer constant expression and the element type has
       * a known constant size, the array type is not a variable length array
       * type" (C11 standard, §6.7.6.2 "Array Declarators"). *)
      if env.warn && not (is_int_constant e2) && lifetime = Common.Stack then begin
        let e = KPrint.bsprintf "%a" pexpr e in
        let loc = KPrint.bsprintf "%a" ploc env.location in
        Warn.(maybe_fatal_error (loc, Vla e))
      end;
      let t, _ = assert_buffer env t in
      let t' = check_or_infer env t e1 in
      if t' = TAny then
        checker_error env buf_any_msg ppexpr e;
      check env t e1;
      check_array_index env e2;
      c (best_buffer_type lifetime t e2)

  | EBufRead (e1, e2) ->
      check_array_index env e2;
      check env (TBuf (t, true)) e1;
      c t

  | EBufWrite (e1, e2, e3) ->
      check_array_index env e2;
      let t1, c1 = infer_buffer env e1 in
      check env t1 e3;
      check_mut env "write" c1;
      c TUnit

  | EBufSub (e1, e2) ->
      check_array_index env e2;
      check_buffer env t e1

  | EBufDiff (e1, e2) ->
      let t1 = infer env e1 in
      check_buffer env t1 e2

  | EBufFill (e1, e2, e3) ->
      let t1, c1 = infer_buffer env e1 in
      check env t1 e2;
      check_mut env "fill" c1;
      check_array_index env e3;
      c TUnit

  | EBufBlit (b1 (* source *), i1, b2 (* destination *), i2, len) ->
      let t1, _ = infer_buffer env b1 in  (* source can be const *)
      check env (TBuf (t1, false)) b2;    (* destination must be non-const *)
      check_array_index env i1;
      check_array_index env i2;
      check_array_index env len;
      c TUnit

  | EBufCreateL (_, es) ->
      let t, _ = assert_buffer env t in
      List.iter (check env t) es

  | EBufFree e ->
      check env (TBuf (TAny, false)) e;
      c TUnit

  | ETuple es ->
      let ts = assert_tuple env t in
      if List.length ts <> List.length es then
        checker_error env "Tuple length mismatch";
      List.iter2 (check env) ts es

  | ECons (ident, exprs) ->
      (** The typing rules of matches and constructors are always nominal;
       * structural types appear through simplification phases, which also
       * remove matches in favor of switches or conditionals. *)
      let t = if t = TAny then e.typ else t in
      begin match expand_abbrev env t with
      | TQualified lid
      | TApp (lid, _) ->
          ignore (assert_variant env (lookup_type env lid))
      | _ ->
          ()
      end;
      let env = locate env (Call ident) in
      let ts' = args_of_branch env t ident in
      List.iter2 (check env) ts' exprs

  | EMatch (_, e, bs) ->
      let t_scrut = infer (locate env Scrutinee) e in
      check_branches env t t_scrut bs

  | EFlat fieldexprs ->
      (** Just like a constructor and a match, a record and field expressions
       * construct and destruct values of matching kinds, except that structural
       * typing comes into play. Indeed, a flat record is typed nominally (if
       * the context demands it) or structurally (default). TODO just type
       * structurally, and let the subtyping relation do the rest? *)
      let t = expand_abbrev env t in
      begin match flatten_tapp t with
      | exception Invalid_argument _ ->
          begin match t with
          | TAnonymous (Flat fieldtyps) ->
              check_fields_opt env fieldexprs fieldtyps
          | TAnonymous (Union fieldtyps) ->
              check_union env fieldexprs fieldtyps
          | _ ->
              checker_error env "Not a record %a" ptyp t
          end

      | lid, ts, cgs when kind env lid = Some Record ->
          let fieldtyps = assert_flat env (lookup_type env lid) in
          let fieldtyps = List.map (fun (field, (typ, m)) ->
            field, (DeBruijn.subst_tn ts (DeBruijn.subst_ctn' cgs typ), m)
          ) fieldtyps in
          check_fields_opt env fieldexprs fieldtyps

      | lid, ts, cgs when kind env lid = Some Union ->
          let fieldtyps = assert_union env (lookup_type env lid) in
          let fieldtyps = List.map (fun (field, typ) ->
            field, DeBruijn.subst_tn ts (DeBruijn.subst_ctn' cgs typ)
          ) fieldtyps in
          check_union env fieldexprs fieldtyps

      | _ ->
          checker_error env "Not a record (2) %a" ptyp t
      end

  | ESwitch (scrut, branches) ->
      let t_scrut = expand_abbrev env (infer env scrut) in
      List.iter (fun (c, e) ->
        check_case (locate env (Branch c)) c t_scrut;
        check env t e
      ) branches;

  | EAddrOf e ->
      let t = infer env e in
      c (TBuf (t, false))


and check_case env c t =
  match c, t with
  | SWild, _ ->
      ()
  | SEnum tag, TQualified lid ->
      if not (M.find tag env.enums = lid) then
        checker_error env "scrutinee has type %a but tag %a does not belong to \
          this type" plid lid plid tag
  | SEnum tag, TAnonymous (Enum tags) ->
      if not (List.exists (fun (tag', _) -> tag' = tag) tags) then
        checker_error env "scrutinee has type %a but tag %a does not belong to \
          this type" ptyp t plid tag
  | SConstant (w, _), TInt w' ->
      if w <> w' then
        checker_error env "scrutinee has type %a but switch case is an %a \
          this type" ptyp t pwidth w
  | _ ->
      checker_error env "case %a cannot switch on element of type %a" pcase c ptyp t


and args_of_branch env t ident =
  match expand_abbrev env t with
  | TQualified lid ->
      fst (List.split (snd (List.split (assert_cons_of env (lookup_type env lid) ident))))
  | TApp (lid, args) ->
      let ts' = fst (List.split (snd (List.split (assert_cons_of env (lookup_type env lid) ident)))) in
      List.map (fun t -> DeBruijn.subst_tn args t) ts'
  | _ ->
      checker_error env "Type annotation is not an lid but %a" ptyp t

and infer env e =
  if Options.debug "checker" then KPrint.bprintf "[infer] %a\n" pexpr e;
  let t = infer' env e in
  if Options.debug "checker" then KPrint.bprintf "[infer, got] %a\n" ptyp t;
  check_subtype env t e.typ;
  (* This is all because of external that retain their polymorphic
     signatures. TODO: does this alleviate the need for those crappy checks in
     subtype? *)
  let t = MonomorphizationState.resolve_deep t in
  e.typ <- prefer_nominal t e.typ;
  if Options.debug "checker" then KPrint.bprintf "[infer, now] %a\n" ptyp e.typ;
  t

and prefer_nominal t1 t2 =
  match t1, t2 with
  | (TQualified _ | TApp _), _ ->
      t1
  | _, (TQualified _ | TApp _) ->
      t2
  | _, _ ->
      t1

and best_buffer_type l t1 e2 =
  match e2.node, l with
  | EConstant k, Common.Stack ->
      TArray (t1, k)
  | _ ->
      TBuf (t1, false)

and infer' env e =
  let infer_app t es =
    let t_ret, t_args = flatten_arrow t in
    if List.length t_args = 0 then
      checker_error env "This is not a function type:\n%a a.k.a. %s\n" ptyp t (show_typ t);
    if List.length es > List.length t_args then
      checker_error env "Too many arguments for application:\n%a" pexprs es;
    let t_args, t_remaining_args = KList.split (List.length es) t_args in
    ignore (List.map2 (check_or_infer env) t_args es);
    fold_arrow t_remaining_args t_ret
  in

  match e.node with
  | ETApp (e0, cs, cs', ts) ->
      begin match e0.node with
      | EOp ((K.Eq | K.Neq), _) ->
          (* Special incorrect encoding of polymorphic equalities *)
          let t = KList.one ts in
          TArrow (t, TArrow (t, TBool))
      | _ ->
          let diff = List.length env.locals - env.n_cgs in
          let t = infer env e0 in
          if Options.debug "checker-cg" then
            KPrint.bprintf "infer-cg: t=%a, cs=%a, ts=%a, diff=%d\n" ptyp t pexprs cs ptyps ts diff;
          let t = match t with
            | TPoly ({ n; n_cgs }, t) ->
                let ts = { n = n - List.length ts; n_cgs = n_cgs - List.length cs } in
                if ts.n > 0 || ts.n_cgs > 0 then
                  TPoly (ts, t)
                else
                  t
            | t ->
                t
          in
          if Options.debug "checker-cg" then
            KPrint.bprintf "infer-cg: chop --> %a\n" ptyp t;
          let t = DeBruijn.subst_ctn diff cs t in
          if Options.debug "checker-cg" then
            KPrint.bprintf "infer-cg: subst_ctn (diff=%d)--> %a\n" diff ptyp t;
          let t = DeBruijn.subst_tn ts t in
          if Options.debug "checker-cg" then
            KPrint.bprintf "infer-cg: subst_tn --> %a\n" ptyp t;
          (* Now type-check the application itself, after substitution *)
          let t =
            match t with
            | TPoly (ts, t) ->
                assert (cs' = []);
                TPoly (ts, infer_app t (cs @ cs'))
            | t ->
                MonomorphizationState.resolve (infer_app t (cs @ cs'))
          in
          if Options.debug "checker-cg" then
            KPrint.bprintf "infer-cg: infer_app --> %a\n" ptyp t;
          t
      end

  | EPolyComp (_, t) ->
      TArrow (t, TArrow (t, TBool))

  | EBound i ->
      begin try
        (find env i).typ
      with Not_found ->
        checker_error env "bound variable %d is malformed" i
      end

  | EOpen (name, _) ->
      checker_error env "there is an open variable %s" name

  | EQualified lid ->
      lookup_global env lid

  | EConstant (w, _) ->
      TInt w

  | EStandaloneComment _ ->
      TUnit

  | EUnit ->
      TUnit

  | ECast (e, t) ->
      if t = TAny then
        Warn.maybe_fatal_error ("", NotLowStarCast e);
      ignore (infer env e);
      t

  | EIgnore e ->
      ignore (infer env e);
      TUnit

  | EApp (e, es) ->
      let env = locate env (Call (KPrint.bsprintf "%a" pexpr e)) in
      let t = infer env e in
      if t = TAny then
        let _ = List.map (infer env) es in
        TAny
      else
        infer_app t es

  | ELet (binder, body, cont) ->
      let t = check_or_infer (locate env (In binder.node.name)) binder.typ body in
      binder.typ <- t;
      let env = push env binder in
      infer (locate env (After binder.node.name)) cont

  | EIfThenElse (e1, e2, e3) ->
      check env TBool e1;
      let t1 = infer (locate env Then) e2 in
      let t2 = infer (locate env Else) e3 in
      check_eqtype env t1 t2;
      (if t1 = TAny then t2 else t1)

  | ESequence es ->
      begin match List.rev es with
      | last :: rest ->
          List.iter (check env TUnit) (List.rev rest);
          infer env last
      | [] ->
          checker_error env "Empty sequence"
      end

  | EAssign (e1, e2) ->
      let t = infer env e1 in
      check_valid_assignment_lhs env e1;
      check env t e2;
      TUnit

  | EBufCreate (l, e1, e2) ->
      let t1 = infer env e1 in
      check_array_index env e2;
      best_buffer_type l t1 e2

  | EBufRead (e1, e2) ->
      check_array_index env e2;
      fst (infer_buffer env e1)

  | EBufWrite (e1, e2, e3) ->
      check_array_index env e2;
      let t1, c = infer_buffer env e1 in
      check_mut env "write" c;
      check env t1 e3;
      TUnit

  | EBufSub (e1, e2) ->
      check_array_index env e2;
      let t1, c = infer_buffer env e1 in
      TBuf (t1, c)

  | EBufDiff (e1, e2) ->
      let t1 = infer env e1 in
      check_buffer env t1 e2;
      TInt PtrdiffT

  | EBufFill (e1, e2, e3) ->
      let t1, c = infer_buffer env e1 in
      check_mut env "fill" c;
      check env t1 e2;
      check_array_index env e3;
      TUnit

  | EBufBlit (b1 (* source *), i1, b2 (* destination *), i2, len) ->
      let t1, _ = infer_buffer env b1 in  (* source can be const *)
      check env (TBuf (t1, false)) b2;    (* destination must be non-const *)
      check_array_index env i1;
      check_array_index env i2;
      check_array_index env len;
      TUnit

  | EBufFree e ->
      ignore (infer_buffer env e);
      TUnit

  | EOp (op, w) ->
      begin try
        type_of_op op w
      with _ ->
        checker_error env "%a, operator %a is for internal use only" ploc env.location pop op
      end

  | EPushFrame | EPopFrame ->
      TUnit

  | EAny | EAbort _ ->
      TAny

  | EReturn e ->
      ignore (infer env e);
      (** TODO: check that [EReturn] matches the expected return type *)
      TAny

  | EContinue
  | EBreak ->
      TUnit

  | EBool _ ->
      TBool

  | EString _ ->
      c_string

  | EWhile (e1, e2) ->
      check env TBool e1;
      let t = infer env e2 in
      if t = TUnit then
        TUnit
      else if t = TAny then
        TAny (* loops that end in return can be typed with TAny *)
      else
        checker_error env "%a, while loop is neither tany or tunit" ploc env.location

  | EBufCreateL (_, es) ->
      begin match es with
      | [] ->
          checker_error env "%a, there is an empty buf create sequence" ploc env.location
      | first :: others ->
          let t = infer env first in
          List.iter (check env t) others;
          TArray (t, (K.UInt32, string_of_int (List.length es)))
      end

  | ETuple es ->
      TTuple (List.map (infer env) es)

  | ECons (ident, args) ->
      begin match expand_abbrev env e.typ with
      | TQualified lid
      | TApp (lid, _) ->
          ignore (assert_variant env (lookup_type env lid))
      | _ ->
          ()
      end;
      let env = locate env (Call ident) in
      ignore (List.map (infer env) args);
      (* Preserve the provided type annotation that (hopefully) was there in the
       * first place. *)
      e.typ

  | EMatch (_, e, bs) ->
      let t_scrut = infer env e in
      infer_branches env t_scrut bs

  | EFlat fieldexprs ->
      prefer_nominal
        e.typ
        (TAnonymous (Flat (List.map (fun (f, e) ->
          f, (infer env e, false)
        ) fieldexprs)))

  | EField (e, field) ->
      (** Structs and unions have fields; they may be typed structurally or
       * nominally, and we shall dereference a field in both cases. *)
      let t = infer env e in
      begin match find_field env t field with
      | Some (t, _) ->
          t
      | None ->
          checker_error env "this type doesn't have fields"
      end

  | EEnum tag ->
      (** Enums / Switches behave just like Flats / Fields; the constructor
       * gives rise to a structural or nominal type and the destructor works
       * with either a nominal or a structural type. *)
      begin try
        TQualified (M.find tag env.enums)
      with Not_found ->
        (* TODO: figure out how this happens? *)
        TAnonymous (Enum [ tag, None ])
      end

  | ESwitch (e1, branches) ->
      let t_scrut = expand_abbrev env (infer env e1) in
      let t = infer_and_check_eq env (fun (c, e) ->
        let env = locate env (Branch c) in
        check_case env c t_scrut;
        infer env e
      ) branches in
      t

  | EFun (binders, e, t_ret) ->
      let env = List.fold_left push env binders in
      check env t_ret e;
      List.fold_right (fun binder t -> TArrow (binder.typ, t)) binders t_ret

  | EFor (binder, e1, e2, e3, e4) ->
      let t = check_or_infer (locate env (In binder.node.name)) binder.typ e1 in
      binder.typ <- t;
      let env = push env binder in
      check (locate env ForCond) TBool e2;
      check (locate env ForIter) TUnit e3;
      check (locate env For) TUnit e4;
      TUnit

  | EAddrOf e ->
      TBuf (infer env e, false)

  | EBufNull ->
      assert (e.typ <> TAny);
      (* e.typ is the type of the whole node, so it's already of the form TBuf _ *)
      e.typ

and infer_and_check_eq: 'a. env -> ('a -> typ) -> 'a list -> typ =
  fun env f l ->
  let t_base = ref None in
  List.iter (fun elt ->
    let t = f elt in
    match !t_base with
    | Some t_base -> check_eqtype env t_base t
    | None -> t_base := Some t
  ) l;
  Option.get !t_base

and find_field env t field =
  let t = expand_abbrev env t in
  match flatten_tapp t with
  | exception Invalid_argument _ ->
      begin match t with
      | TAnonymous def ->
          Some (find_field_from_def env def field)
      | _ ->
          None
      end
  | lid, ts, cgs ->
      let t, mut = find_field_from_def env (lookup_type env lid) field in
      Some (DeBruijn.(subst_tn ts (subst_ctn' cgs t), mut))

and find_field_from_def env def field =
  try begin match def with
    | Union fields ->
        List.assoc field fields, true (* owing to nocompound-literals which may mutate it *)
    | Flat fields ->
        List.assoc (Some field) fields
    | _ ->
        raise Not_found
  end with Not_found ->
    checker_error env "record or union type %a doesn't have a field named %s" ptyp (TAnonymous def) field


(* Per Perry's definition, a path is a block id along with an offset, and a
 * possibly empty sequence of field names. We don't check (TODO) that after
 * rewritings, all paths are of that form. *)

(** This function checks that the left-hand side of assignments satisfies a
 * relaxed notion of path (to be formalized), which is either a locally mutable
 * variable (an extension on Perry's formalism) or an array access followed by a
 * non-empty series of field names, the last of which is mutable. *)
and check_valid_assignment_lhs env e =
  match e.node with
  | EBound i ->
      let binder = find env i in
      if not binder.node.mut then
        checker_error env "%a (a.k.a. %s) is not a mutable binding" pexpr e binder.node.name
  | EField (e, f) ->
      let t1 = check_valid_path env e in
      begin match find_field env t1 f with
      | Some (_, mut) ->
          if not mut then
            checker_error env "the field %s of type %a is not marked as mutable" f ptyp t1
      | None ->
          checker_error env "field not found %s" f
      end
  | EBufRead _
      (* Introduced by the wasm struct allocation phase. *)
  | EQualified _
      (* Introduced when collecting global initializers. *)
  | EApp ({ node = ETApp _; _ }, _) ->
      (* Will be emitted as a macro, optimistically assuming that's ok, the C
         compiler will bark if not. *)
      ()
  | _ ->
      checker_error env "EAssign wants a lhs that's a mutable, local variable, or a \
        path to a mutable field; got %a instead" pexpr e

and check_valid_path env e =
  match e.node with
  | EField (e, f) ->
      let t1 = check_valid_path env e in
      fst (Option.get (find_field env t1 f))

  | EBufRead _
  | EBound _ ->
      infer env e

  | _ ->
      checker_error env "EAssign wants a lhs that's a mutable, local variable, or a \
        path to a mutable field"

and check_branches env t_context t_scrutinee branches =
  List.iter (fun (binders, pat, expr) ->
    let env = List.fold_left push env binders in
    check_pat env t_scrutinee pat;
    check env t_context expr
  ) branches

and infer_branches env t_scrutinee branches =
  infer_and_check_eq env (fun (binders, pat, expr) ->
    let env = List.fold_left push env binders in
    check_pat env t_scrutinee pat;
    infer env expr
  ) branches

and check_pat env t_context pat =
  (* KPrint.bprintf "Checking pattern: %a\n" ppat pat; *)
  (* KPrint.bprintf "t_context:%a\n" ptyp t_context; *)
  match pat.node with
  | PWild ->
      pat.typ <- t_context

  | PBound i ->
      let b = find env i in
      check_subtype env t_context b.typ;
      b.typ <- t_context;
      check_subtype env t_context pat.typ;
      pat.typ <- t_context

  | POpen _ ->
      failwith "checker does not open patterns"

  | PUnit ->
      check_subtype env t_context TUnit;
      pat.typ <- t_context

  | PBool _ ->
      check_subtype env t_context TBool;
      pat.typ <- t_context

  | PTuple ps ->
      let ts = assert_tuple env t_context in
      List.iter2 (check_pat env) ts ps;
      pat.typ <- t_context

  | PCons (ident, pats) ->
      let ts = args_of_branch env t_context ident in
      List.iter2 (check_pat env) ts pats;
      pat.typ <- t_context

  | PRecord fieldpats ->
      begin match expand_abbrev env t_context with
      | TQualified lid when kind env lid = Some Record ->
          (* KPrint.bprintf "lid: %a\ndef: %a\n" *)
          (*   plid lid *)
          (*   pdef (lookup_type env lid); *)
          let fieldtyps = assert_flat env (lookup_type env lid) in
          check_fieldpats env fieldpats fieldtyps
      | TApp (lid, ts) when kind env lid = Some Record ->
          let fieldtyps = assert_flat env (lookup_type env lid) in
          let fieldtyps = List.map (fun (field, (typ, m)) ->
            field, (DeBruijn.subst_tn ts typ, m)
          ) fieldtyps in
          check_fieldpats env fieldpats fieldtyps
      | TAnonymous (Flat fieldtyps) ->
          check_fieldpats env fieldpats fieldtyps
      | _ ->
          checker_error env "Not a record %a" ptyp t_context
      end;
      pat.typ <- t_context

  | PEnum tag ->
      let lid = assert_qualified env t_context in
      assert (lid = M.find tag env.enums);
      pat.typ <- t_context

  | PDeref p ->
      let t, _ = assert_buffer env t_context in
      check_pat env t p;
      pat.typ <- t_context;

  | PConstant (w, _) ->
      check_subtype env t_context (TInt w);
      pat.typ <- TInt w


and assert_tuple env t =
  match expand_abbrev env t with
  | TTuple ts ->
      ts
  | _ ->
      checker_error env "%a is not a tuple type" ptyp t

and assert_variant env t =
  match t with
  | Variant def ->
      def
  | _ ->
      checker_error env "%a, this is not a variant definition: %a" ploc env.location pdef t

and assert_flat env t =
  match t with
  | Flat def ->
      def
  | _ ->
      checker_error env "%a, %a is not a record definition" ploc env.location pdef t

and assert_union env t =
  match t with
  | Union def ->
      def
  | _ ->
      checker_error env "%a, %a is not a union definition" ploc env.location pdef t

and assert_qualified env t =
  match expand_abbrev env t with
  | TQualified lid ->
      lid
  | _ ->
      checker_error env "%a, expected a provided type annotation, got %a" ploc env.location ptyp t

and assert_buffer env t =
  match expand_abbrev env t with
  | TBuf (t1, b) ->
      t1, b
  | TArray (t1, _) ->
      t1, false
  | TCgArray (t1, _) ->
      t1, false
  | t ->
      checker_error env "This is not a buffer: %a" ptyp t

and infer_buffer env e1 =
  assert_buffer env (infer env e1)

and check_buffer env t e1 =
  let t, c = assert_buffer env t in
  check env (TBuf (t, c)) e1

and assert_cons_of env t id: fields_t =
  match t with
  | Variant branches ->
      begin try
        List.assoc id branches
      with Not_found ->
        checker_error env "%s is not a constructor of the annotated type %a" id ptyp (TAnonymous t)
      end
  | _ ->
      checker_error env "the annotated type %a is not a variant type" ptyp (TAnonymous t)

and subtype env t1 t2 =
  let normalize t =
    match MonomorphizationState.resolve_deep (expand_abbrev env t) with
    | TBuf (TApp ((["Eurydice"], "derefed_slice"), [ t ]), _) ->
        TApp ((["Eurydice"], "slice"), [t])
    | t ->
        t
  in
  let t1 = normalize t1 in
  let t2 = normalize t2 in
  if Options.debug "checker" then
    KPrint.bprintf "%a <=? %a\n" ptyp t1 ptyp t2;
  match t1, t2 with
  | TInt w1, TInt w2 when w1 = w2 ->
      true
  | TInt K.SizeT, TInt K.UInt32 when Options.wasm () ->
      true
  | TInt K.UInt32, TInt K.SizeT when Options.wasm () ->
      true
  | TArray (t1, (_, l1)), TArray (t2, (_, l2)) when subtype env t1 t2 && l1 = l2 ->
      true
  | TCgArray (t1, l1), TCgArray (t2, l2) when subtype env t1 t2 && l1 = l2 ->
      true
  | TBuf (t1, _), TCgArray (t2, _)
  | TCgArray (t1, _), TBuf (t2, _) when subtype env t1 t2 ->
      true
  | TBuf (t1, _), TArray (t2, _)
  | TArray (t1, _), TBuf (t2, _) when subtype env t1 t2 ->
      true
  | TBuf (t1, b1), TBuf (t2, b2) when subtype env t1 t2 && (b1 <= b2) ->
      true
  | TUnit, TUnit ->
      true
  | TQualified lid1, TQualified lid2 ->
      lid1 = lid2
  | TBool, TBool
  | _, TQualified (["FStar"; "Dyn"], "dyn")
  | TQualified (["FStar"; "Dyn"], "dyn"), _
  | _, TAny
  | TAny, _ ->
      true
  | TArrow (t1, t2), TArrow (t'1, t'2) when
    subtype env t1 t'1 &&
    subtype env t2 t'2 ->
      true
  | TBound i, TBound i' ->
      i = i'
  | TApp (lid, args), TApp (lid', args') ->
      lid = lid' && List.for_all2 (eqtype env) args args'
  | TCgApp (lid, args), TCgApp (lid', args') ->
      subtype env lid lid' && args = args'
  | TTuple ts1, TTuple ts2 ->
      List.length ts1 = List.length ts2 &&
      List.for_all2 (subtype env) ts1 ts2

  | TAnonymous ((Enum _ | Union _ | Flat _)), TQualified lid ->
      begin try
        subtype env t1 (TAnonymous (M.find lid env.types))
      with Not_found ->
        false
      end

  | TAnonymous ((Enum _ | Union _ | Flat _)), TApp (lid, targs) ->
      begin try
        let t2 = DeBruijn.subst_tn targs (TAnonymous (M.find lid env.types)) in
        subtype env t1 t2
      with Not_found ->
        false
      end

  | TAnonymous (Enum tags1), TAnonymous (Enum tags2) ->
      List.for_all (fun t1 -> List.mem t1 tags2) tags1

  | TAnonymous (Union fields1), TAnonymous (Union fields2) ->
      List.length fields1 = List.length fields2 &&
      List.for_all2 (fun (f1, t1) (f2, t2) ->
        f1 = f2 && subtype env t1 t2
      ) fields1 fields2

  | TAnonymous (Flat fields1), TAnonymous (Flat fields2) ->
      List.length fields1 = List.length fields2 &&
      List.for_all2 (fun (f1, (t1, _)) (f2, (t2, _)) ->
        f1 = f2 && subtype env t1 t2
      ) fields1 fields2

  | TAnonymous (Flat [ Some f, (t, _) ]), TAnonymous (Union ts) ->
      List.exists (fun (f', t') -> f = f' && subtype env t t') ts

  | TPoly (ts1, t1), TPoly (ts2, t2) ->
      ts1 = ts2 && subtype env t1 t2

  (* TEMPORARY until we have unifor treatment of type schemes in Eurydice *)
  | t1, TPoly (_, t2) ->
      subtype env t1 t2

  (* TEMPORARY until we have unifor treatment of type schemes in Eurydice *)
  | TPoly (_, t2), t1 ->
      subtype env t2 t1

  | _ ->
      if Options.debug "checker" then
        MonomorphizationState.debug ();
      false

and eqtype env t1 t2 =
  subtype env t1 t2 && subtype env t2 t1

and check_eqtype env t1 t2 =
  if not (eqtype env t1 t2) then
    checker_error env "eqtype mismatch, %a (a.k.a. %a) vs %a (a.k.a. %a)"
      ptyp t1 ptyp (expand_abbrev env t1) ptyp t2 ptyp (expand_abbrev env t2)

and check_subtype env t1 t2 =
  if not (subtype env t1 t2) then
    checker_error env "subtype mismatch:\n  %a (a.k.a. %a) vs:\n  %a (a.k.a. %a)"
      ptyp t1 ptyp (expand_abbrev env t1) ptyp t2 ptyp (expand_abbrev env t2)

and expand_abbrev env t =
  match t with
  | TQualified lid ->
      begin match M.find lid env.types with
      | exception Not_found -> t
      | Abbrev t -> expand_abbrev env t
      | _ -> t
      end
  | TApp (lid, args) ->
      begin match M.find lid env.types with
      | exception Not_found -> TApp (lid, List.map (expand_abbrev env) args)
      | Abbrev t -> expand_abbrev env (DeBruijn.subst_tn args t)
      | _ -> TApp (lid, List.map (expand_abbrev env) args)
      end
  | _ ->
      t

and check_array_index env e =
    match check env uint32 e with
    | exception CheckerError _ -> check env sizet e
    | x -> x


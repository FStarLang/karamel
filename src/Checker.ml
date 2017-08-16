(** Checking the well-formedness of a program in [Ast] *)

(** TODO this module needs to be rewritten properly with constraints and
 * everything; the bidirectional algorithm is remarkably poor and extremely
 * fragile! *)

open Ast
open Warnings
open Constant
open Location
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

exception UnboundLid of lident

module M = Map.Make(struct
  type t = lident
  let compare = compare
end)

let uint32 = TInt UInt32
let c_string = TQualified ([ "C" ], "string")

type env = {
  globals: typ M.t;
  locals: binder list;
  types: type_def M.t;
  location: loc list;
  enums: lident M.t;
  warn: bool;
}

let empty: env = {
  globals = M.empty;
  locals = [];
  types = M.empty;
  location = [];
  enums = M.empty;
  warn = false
}

let push env binder =
  (* KPrint.bprintf "pushing %s at type %a\n" binder.node.name ptyp binder.typ; *)
  { env with locals = binder :: env.locals }

let find env i =
  List.nth env.locals i

let lookup_type env lid =
  match M.find lid env.types with
  | exception Not_found ->
      raise (UnboundLid lid)
  | x ->
      x

let possibly_warn =
  let h = Hashtbl.create 41 in
  fun env lid ->
    match Hashtbl.find h lid with
    | exception Not_found ->
        Hashtbl.add h lid ();
        maybe_fatal_error (KPrint.bsprintf "%a" ploc env.location,
          UnboundReference (KPrint.bsprintf "%a" plid lid))
    | () ->
        ()

let lookup_global env lid =
  match M.find lid env.globals with
  | exception Not_found ->
      possibly_warn env lid;
      TAny
  | x ->
      x

let populate_env files =
  List.fold_left (fun env (_, decls) ->
    List.fold_left (fun env decl ->
      match decl with
      | DType (lid, _, _, typ) ->
          let env = match typ with
          | Enum tags ->
              List.fold_left (fun env tag ->
                { env with enums = M.add tag lid env.enums }
              ) env tags
          | _ ->
              env
          in
          { env with types = M.add lid typ env.types }
      | DGlobal (_, lid, t, _) ->
          { env with globals = M.add lid t env.globals }
      | DFunction (_, _, n, ret, lid, binders, _) ->
          assert (n = 0);
          let t = List.fold_right (fun b t2 -> TArrow (b.typ, t2)) binders ret in
          { env with globals = M.add lid t env.globals }
      | DExternal (_, lid, typ) ->
          { env with globals = M.add lid typ env.globals }
    ) env decls
  ) empty files

let known_type env lid =
  M.mem lid env.types

let locate env loc =
  { env with location = update_location env.location loc }

(** Errors ------------------------------------------------------------------ *)

let type_error env fmt =
  Printf.kbprintf (fun buf ->
    raise_error_l (KPrint.bsprintf "%a" ploc env.location, TypeError (Buffer.contents buf))
  ) (Buffer.create 16) fmt

(** Checking ---------------------------------------------------------------- *)

let rec check_everything ?warn files: bool * file list =
  let env = populate_env files in
  let env = match warn with Some true -> { env with warn = true } | _ -> env in
  let r = ref false in
  !r, List.map (check_program env r) files

and check_program env r (name, decls) =
  let env = locate env (File name) in
  let by_lid = Hashtbl.create 41 in
  let decls = KList.filter_map (fun d ->
    let lid = lid_of_decl d in
    try
      check_decl env d;
      Some d
    with
    | Error e ->
        if not (Drop.lid lid) then begin
          r := true;
          Warnings.maybe_fatal_error e;
          if Options.debug "backtraces" then
            Printexc.print_backtrace stderr;
          flush stdout;
          KPrint.beprintf "Dropping %a (at checking time); if this is normal, \
            please consider using -drop\n\n"
            plid (lid_of_decl d);
          flush stderr
        end;
        None

    | UnboundLid lid' ->
        if not (Drop.lid lid) then begin
          r := true;
          begin try
            Hashtbl.add by_lid lid' (lid :: Hashtbl.find by_lid lid');
          with Not_found ->
            Hashtbl.add by_lid lid' [ lid ];
          end
        end;
        None

    | e ->
        if not (Drop.lid lid) then begin
          r := true;
          let e = Printexc.to_string e in
          Warnings.maybe_fatal_error ("<toplevel>", TypeError e);
          if Options.debug "backtraces" then
            Printexc.print_backtrace stderr;
          flush stdout;
          KPrint.beprintf "Dropping %a (at checking time); if this is normal, \
            please consider using -drop\n\n"
            plid (lid_of_decl d);
          flush stderr
        end;
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
      flow break1 (words "meaning that they cannot be type-checked by KreMLin; \
        if this is normal, please consider using -drop")
    )
  ) by_lid;

  name, decls


and check_decl env d =
  match d with
  | DFunction (_, _, n, t, name, binders, body) ->
      assert (n = 0);
      let env = List.fold_left push env binders in
      let env = locate env (InTop name) in
      check env t body
  | DGlobal (_, name, t, body) ->
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

and check env t e =
  (* KPrint.bprintf "[check] %a for %a\n" ptyp t pexpr e; *)
  check' env t e;
  e.typ <- t

and check' env t e =
  let c t' = check_subtype env t' t in
  match e.node with
  | ETApp _ ->
      assert false

  | EBound _
  | EOpen _
  | EQualified _
  | EConstant _
  | ECast _
  | EUnit
  | EAssign _
  | EOp _
  | EPushFrame | EPopFrame
  | EAny | EAbort _
  | EReturn _
  | EBreak
  | EBool _
  | EWhile _
  | EEnum _
  | EField _
  | EString _
  | EFun _
  | EFor _
  | EIgnore _
  | EApp _ ->
      c (infer env e)

  | EComment (_, e, _) ->
      check env t e

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
          type_error env "Empty sequence"
      end

  | EBufCreate (_, e1, e2) ->
      if env.warn && not (is_constant e2) then begin
        let e = KPrint.bsprintf "%a" pexpr e in
        let loc = KPrint.bsprintf "%a" ploc env.location in
        Warnings.(maybe_fatal_error (loc, Vla e))
      end;
      let t = assert_buffer env t in
      if t = TAny then
        type_error env buf_any_msg ppexpr e;
      check env t e1;
      check env uint32 e2;
      c (best_buffer_type t e2)

  | EBufRead (e1, e2) ->
      check env uint32 e2;
      check env (TBuf t) e1

  | EBufWrite (e1, e2, e3) ->
      check env uint32 e2;
      let t1 = infer_buffer env e1 in
      check env t1 e3;
      c TUnit

  | EBufSub (e1, e2) ->
      check env uint32 e2;
      check_buffer env t e1

  | EBufFill (e1, e2, e3) ->
      let t1 = infer_buffer env e1 in
      check env t1 e2;
      check env uint32 e3;
      c TUnit

  | EBufBlit (b1, i1, b2, i2, len) ->
      let t1 = infer_buffer env b1 in
      check env (TBuf t1) b2;
      check env uint32 i1;
      check env uint32 i2;
      check env uint32 len;
      c TUnit

  | EBufCreateL (_, es) ->
      let t = assert_buffer env t in
      List.iter (check env t) es

  | ETuple es ->
      let ts = assert_tuple env t in
      if List.length ts <> List.length es then
        type_error env "Tuple length mismatch";
      List.iter2 (check env) ts es

  | ECons (ident, exprs) ->
      (** The typing rules of matches and constructors are always nominal;
       * structural types appear through simplification phases, which also
       * remove matches in favor of switches or conditionals. *)
      begin match expand_abbrev env t with
      | TQualified lid
      | TApp (lid, _) ->
          ignore (assert_variant env (lookup_type env lid))
      | _ ->
          ()
      end;
      let ts' = args_of_branch env t ident in
      List.iter2 (check env) ts' exprs

  | EMatch (e, bs) ->
      let t_scrut = infer (locate env Scrutinee) e in
      check_branches env t t_scrut bs

  | EFlat fieldexprs ->
      (** Just like a constructor and a match, a record and field expressions
       * construct and destruct values of matching kinds, except that structural
       * typing comes into play. Indeed, a flat record is typed nominally (if
       * the context demands it) or structurally (default). TODO just type
       * structurally, and let the subtyping relation do the rest? *)
      let check_fields fieldexprs fieldtyps =
        if List.length fieldexprs > List.length fieldtyps then
          type_error env "some fields are superfluous";
        List.iter (fun (field, expr) ->
          let field = Option.must field in
          let t, _ = KList.assoc_opt field fieldtyps in
          check env t expr
        ) fieldexprs
      in
      begin match expand_abbrev env t with
      | TQualified lid ->
          let fieldtyps = assert_flat env (lookup_type env lid) in
          check_fields fieldexprs fieldtyps
      | TApp (lid, ts) ->
          let fieldtyps = assert_flat env (lookup_type env lid) in
          let fieldtyps = List.map (fun (field, (typ, m)) ->
            field, (DeBruijn.subst_tn ts typ, m)
          ) fieldtyps in
          check_fields fieldexprs fieldtyps
      | TAnonymous (Flat fieldtyps) ->
          check_fields fieldexprs fieldtyps
      | TAnonymous (Union fieldtyps) ->
          begin match fieldexprs with
          | [ Some f, e ] ->
              begin try
                check env (List.assoc f fieldtyps) e
              with Not_found ->
                type_error env "Union does not have such a field"
              end
          | [ None, { node = EConstant (_, "0"); _ } ] ->
              ()
          | _ ->
              type_error env "Union expected, i.e. exactly one provided field";
          end
      | _ ->
          type_error env "Not a record %a" ptyp t
      end

  | ESwitch (e, branches) ->
      begin match infer env e with
      | TQualified lid ->
          List.iter (fun (tag, e) ->
            check env t e;
            if not (M.find tag env.enums = lid) then
              type_error env "scrutinee has type %a but tag %a does not belong to \
                this type" plid lid plid tag
          ) branches

      | TAnonymous (Enum tags) as t' ->
          List.iter (fun (tag, e) ->
            check env t e;
            if not (List.exists ((=) tag) tags) then
              type_error env "scrutinee has type %a but tag %a does not belong to \
                this type" ptyp t' plid tag
          ) branches

      | t ->
          type_error env "cannot switch on element of type %a" ptyp t
      end

  | EAddrOf e ->
      let t = infer env e in
      c (TBuf t)

and args_of_branch env t ident =
  match expand_abbrev env t with
  | TQualified lid ->
      fst (List.split (snd (List.split (assert_cons_of env (lookup_type env lid) ident))))
  | TApp (lid, args) ->
      let ts' = fst (List.split (snd (List.split (assert_cons_of env (lookup_type env lid) ident)))) in
      List.map (fun t -> DeBruijn.subst_tn args t) ts'
  | _ ->
      type_error env "Type annotation is not an lid but %a" ptyp t

and infer env e =
  (* KPrint.bprintf "[infer] %a\n" pexpr e; *)
  let t = infer' env e in
  (* KPrint.bprintf "[infer, got] %a\n" ptyp t; *)
  check_subtype env t e.typ;
  e.typ <- prefer_nominal t e.typ;
  t

and prefer_nominal t1 t2 =
  match t1, t2 with
  | (TQualified _ | TApp _), _ ->
      t1
  | _, (TQualified _ | TApp _) ->
      t2
  | _, _ ->
      t1

and best_buffer_type t1 e2 =
  match e2.node with
  | EConstant k ->
      TArray (t1, k)
  | _ ->
      TBuf t1


and infer' env e =
  match e.node with
  | ETApp _ ->
      assert false

  | EBound i ->
      begin try
        (find env i).typ
      with Not_found ->
        type_error env "bound variable %d is malformed" i
      end

  | EOpen (name, _) ->
      type_error env "there is an open variable %s" name

  | EQualified lid ->
      lookup_global env lid

  | EConstant (w, _) ->
      TInt w

  | EUnit ->
      TUnit

  | ECast (e, t) ->
      ignore (infer env e);
      t

  | EIgnore e ->
      ignore (infer env e);
      TUnit

  | EApp (e, es) ->
      let t = infer env e in
      if t = TAny then
        let _ = List.map (infer env) es in
        TAny
      else
        let t_ret, t_args = flatten_arrow t in
        if List.length t_args = 0 then
          type_error env "This is not a function:\n%a" pexpr e;
        if List.length es > List.length t_args then
          type_error env "Too many arguments for application:\n%a" pexpr e;
        let t_args, t_remaining_args = KList.split (List.length es) t_args in
        List.iter2 (check env) t_args es;
        fold_arrow t_remaining_args t_ret

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
      t1

  | ESequence es ->
      begin match List.rev es with
      | last :: rest ->
          List.iter (check env TUnit) (List.rev rest);
          infer env last
      | [] ->
          type_error env "Empty sequence"
      end

  | EAssign (e1, e2) ->
      let t = check_valid_assignment_lhs env e1 in
      check env t e2;
      TUnit

  | EBufCreate (_, e1, e2) ->
      let t1 = infer env e1 in
      check env uint32 e2;
      best_buffer_type t1 e2

  | EBufRead (e1, e2) ->
      check env uint32 e2;
      infer_buffer env e1

  | EBufWrite (e1, e2, e3) ->
      check env uint32 e2;
      let t1 = infer_buffer env e1 in
      check env t1 e3;
      TUnit

  | EBufSub (e1, e2) ->
      check env uint32 e2;
      let t1 = infer_buffer env e1 in
      TBuf t1

  | EBufFill (e1, e2, e3) ->
      let t1 = infer_buffer env e1 in
      check env t1 e2;
      check env uint32 e3;
      TUnit

  | EBufBlit (b1, i1, b2, i2, len) ->
      let t1 = infer_buffer env b1 in
      check env (TBuf t1) b2;
      check env uint32 i1;
      check env uint32 i2;
      check env uint32 len;
      TUnit

  | EOp (op, w) ->
      begin try
        type_of_op op w
      with _ ->
        fatal_error "%a, operator %a is for internal use only" ploc env.location pop op
      end

  | EPushFrame | EPopFrame ->
      TUnit

  | EAny | EAbort _ ->
      TAny

  | EReturn e ->
      ignore (infer env e);
      (** TODO: check that [EReturn] matches the expected return type *)
      TAny

  | EBreak ->
      TUnit

  | EBool _ ->
      TBool

  | EString _ ->
      c_string

  | EWhile (e1, e2) ->
      check env TBool e1;
      check env TUnit e2;
      TUnit

  | EBufCreateL (_, es) ->
      begin match es with
      | [] ->
          fatal_error "%a, there is an empty buf create sequence" ploc env.location
      | first :: others ->
          let t = infer env first in
          List.iter (check env t) others;
          TArray (t, (K.UInt32, string_of_int (List.length es)))
      end

  | ETuple es ->
      TTuple (List.map (infer env) es)

  | ECons _ ->
      begin match expand_abbrev env e.typ with
      | TQualified lid
      | TApp (lid, _) ->
          ignore (assert_variant env (lookup_type env lid))
      | _ ->
          ()
      end;
      (* Preserve the provided type annotation that (hopefully) was there in the
       * first place. *)
      e.typ

  | EMatch (e, bs) ->
      let t_scrutinee = infer env e in
      infer_branches env t_scrutinee bs

  | EFlat fieldexprs ->
      TAnonymous (Flat (List.map (fun (f, e) ->
        f, (infer env e, false)
      ) fieldexprs))

  | EField (e, field) ->
      (** Structs and unions have fields; they may be typed structurally or
       * nominally, and we shall dereference a field in both cases. *)
      let t = infer env e in
      begin match expand_abbrev env t with
      | TQualified lid ->
          fst (find_field env lid field)
      | TApp (lid, ts) ->
          let t = fst (find_field env lid field) in
          DeBruijn.subst_tn ts t
      | TAnonymous def ->
          fst (find_field_from_def env def field)
      | _ ->
          type_error env "this type doesn't have fields"
      end

  | EEnum tag ->
      (** Enums / Switches behave just like Flats / Fields; the constructor
       * gives rise to a structural or nominal type and the destructor works
       * with either a nominal or a structural type. *)
      begin try
        TQualified (M.find tag env.enums)
      with Not_found ->
        TAnonymous (Enum [ tag ])
      end

  | ESwitch (e, branches) ->
      begin match expand_abbrev env (infer env e) with
      | TQualified lid ->
          infer_and_check_eq env (fun (tag, e) ->
            let env = locate env (Branch tag) in
            if not (M.find tag env.enums = lid) then
              type_error env "scrutinee has type %a but tag %a does not belong to \
                this type" plid lid plid tag;
            infer env e
          ) branches

      | TAnonymous (Enum tags) as t ->
          infer_and_check_eq env (fun (tag, e) ->
            let env = locate env (Branch tag) in
            if not (List.exists ((=) tag) tags) then
              type_error env "scrutinee has type %a but tag %a does not belong to \
                this type" ptyp t plid tag;
            infer env e
          ) branches

      | t ->
          type_error env "cannot switch on element of type %a" ptyp t
      end

  | EComment (_, e, _) ->
      infer env e

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
      TBuf (infer env e)

and infer_and_check_eq: 'a. env -> ('a -> typ) -> 'a list -> typ =
  fun env f l ->
  let t_base = ref None in
  List.iter (fun elt ->
    let t = f elt in
    match !t_base with
    | Some t_base -> check_eqtype env t_base t
    | None -> t_base := Some t
  ) l;
  Option.must !t_base

and find_field env lid field =
  find_field_from_def env (lookup_type env lid) field

and find_field_from_def env def field =
  try begin match def with
    | Union fields ->
        List.assoc field fields, false (* not mutable *)
    | Flat fields ->
        KList.assoc_opt field fields
    | _ ->
        raise Not_found
  end with Not_found ->
    type_error env "record or union type %a doesn't have a field named %s" ptyp (TAnonymous def) field


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
        type_error env "%a (a.k.a. %s) is not a mutable binding" pexpr e binder.node.name;
      binder.typ
  | EField (e, f) ->
      let t1 = check_valid_path env e in
      let t2, mut = find_field env (assert_qualified env t1) f in
      if not mut then
        type_error env "the field %s of type %a is not marked as mutable" f ptyp t1;
      t2
  | EBufRead _ ->
      (* Introduced by the wasm struct allocation phase. *)
      e.typ
  | EQualified _ ->
      (* Introduced when collecting global initializers. *)
      e.typ
  | _ ->
      type_error env "EAssign wants a lhs that's a mutable, local variable, or a \
        path to a mutable field; got %a instead" pexpr e

and check_valid_path env e =
  match e.node with
  | EField (e, f) ->
      let t1 = check_valid_path env e in
      fst (find_field env (assert_qualified env t1) f)

  | EBufRead _
  | EBound _ ->
      infer env e

  | _ ->
      type_error env "EAssign wants a lhs that's a mutable, local variable, or a \
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
      let lid = assert_qualified env t_context in
      let fieldtyps = assert_flat env (lookup_type env lid) in
      List.iter (fun ((field, pat): ident * pattern) ->
        let t, _ =
          try
            KList.assoc_opt field fieldtyps
          with Not_found ->
            fatal_error "%a, type %a has no field named %s" ploc env.location plid lid field
        in
        check_pat env t pat
      ) fieldpats;
      pat.typ <- t_context

  | PEnum tag ->
      let lid = assert_qualified env t_context in
      assert (lid = M.find tag env.enums);
      pat.typ <- t_context

  | PDeref p ->
      let t = assert_buffer env t_context in
      check_pat env t p;
      pat.typ <- t_context;


and assert_tuple env t =
  match expand_abbrev env t with
  | TTuple ts ->
      ts
  | _ ->
      type_error env "%a is not a tuple type" ptyp t

and assert_variant env t =
  match t with
  | Variant def ->
      def
  | _ ->
      fatal_error "%a, this is not a variant definition: %a" ploc env.location pdef t

and assert_flat env t =
  match t with
  | Flat def ->
      def
  | _ ->
      fatal_error "%a, %a is not a record definition" ploc env.location pdef t

and assert_qualified env t =
  match expand_abbrev env t with
  | TQualified lid ->
      lid
  | _ ->
      fatal_error "%a, expected a provided type annotation" ploc env.location

and assert_buffer env t =
  match expand_abbrev env t with
  | TBuf t1 ->
      t1
  | TArray (t1, _) ->
      t1
  | t ->
      type_error env "This is not a buffer: %a" ptyp t

and infer_buffer env e1 =
  assert_buffer env (infer env e1)

and check_buffer env t e1 =
  let t = assert_buffer env t in
  check env (TBuf t) e1

and assert_cons_of env t id: fields_t =
  match t with
  | Variant branches ->
      begin try
        List.assoc id branches
      with Not_found ->
        type_error env "%s is not a constructor of the annotated type %a" id ptyp (TAnonymous t)
      end
  | _ ->
      type_error env "the annotated type %a is not a variant type" ptyp (TAnonymous t)

and subtype env t1 t2 =
  match expand_abbrev env t1, expand_abbrev env t2 with
  | TInt w1, TInt w2 when w1 = w2 ->
      true
  | TArray (t1, (_, l1)), TArray (t2, (_, l2)) when subtype env t1 t2 && l1 = l2 ->
      true
  | TArray (t1, _), TBuf t2
  | TBuf t1, TBuf t2 when subtype env t1 t2 ->
      true
  | TUnit, TUnit ->
      true
  | TQualified lid, _
  | TApp (lid, _), _ when not (known_type env lid) ->
      (* God bless Warning 57. *)
      true
  | _, TApp (lid, _)
  | _, TQualified lid when not (known_type env lid) ->
      true
  | TQualified lid1, TQualified lid2 ->
      lid1 = lid2
  | TBool, TBool
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

  | _ ->
      false

and eqtype env t1 t2 =
  subtype env t1 t2 && subtype env t2 t1

and check_eqtype env t1 t2 =
  if not (eqtype env t1 t2) then
    type_error env "eqtype mismatch, %a (a.k.a. %a) vs %a (a.k.a. %a)"
      ptyp t1 ptyp (expand_abbrev env t1) ptyp t2 ptyp (expand_abbrev env t2)

and check_subtype env t1 t2 =
  if not (subtype env t1 t2) then
    type_error env "subtype mismatch, %a (a.k.a. %a) vs %a (a.k.a. %a)"
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

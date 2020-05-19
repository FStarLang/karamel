(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 License. *)

(** Make sure all structures are passed by reference  **************************)

(* A note on this rewriting. We rewrite:
     f e
   into
     let arg = e in
     f &arg
   Then, in the body of [f], we replace every occurrence of its first formal
   parameter [x] with [*x]. THIS IS LEGAL ONLY BECAUSE STRUCTURES SO FAR ARE
   IMMUTABLE. *)

open Ast
open Common
open PrintAst.Ops

(* This pass assumes that all the desugarings that produce structs have run;
 * that type abbreviations have been removed. *)

(* Construct a [typ -> bool] that tells whether this is a struct type or not. *)
let mk_is_struct files =
  let map = Hashtbl.create 41 in
  List.iter (fun (_, decls) ->
    List.iter (function
      | DType (lid, _, _, Flat _)  ->
          Hashtbl.add map lid true
      | _ ->
          ()
    ) decls
  ) files;
  function
    | TAnonymous (Flat _) ->
        true
    | TQualified lid ->
        begin try
          Hashtbl.find map lid
        with Not_found ->
          List.exists (fun lid' ->
            lid = lid' ||
            fst lid = fst lid' && KString.starts_with (snd lid) (snd lid' ^ "__")
          ) !Options.by_ref
        end
    | _ ->
        false

let will_be_lvalue e =
  match e.node with
  | EBound _ | EOpen _ | EBufRead _ ->
      true
  | _ ->
      false

exception NotLowStar

let analyze_function_type is_struct = function
  | TArrow _ as t ->
      let ret, args = Helpers.flatten_arrow t in
      let ret_is_struct = is_struct ret in
      let args_are_structs = List.map is_struct args in
      ret_is_struct, args_are_structs
  | t ->
      Warn.fatal_error "analyze_function_type: %a is not a function type" ptyp t

(* A comment about the insertion of const pointers. Declaring variables with a
 * const qualifier exposes us to some risk of undefined behavior if someone
 * casts the const qualifier away. See comments in LowStar.ConstBuffer.
 *
 * However, since these are variables that *WE* insert, we know that the dangerous
 * cast (to_buffer and to_ibuffer) is not available; therefore, it is ok to
 * declare them with a const qualifier. *)


(* Rewrite functions and expressions to take and possibly return struct
 * pointers. This transformation is entirely type-based. *)
let pass_by_ref is_struct = object (self)

  (* We open all the parameters of a function; then, we pass down as the
   * environment the list of atoms that correspond to by-ref parameters. These
   * will have to be "starred". *)
  inherit [_] map

  (* Rewrite a function type to take and possibly return struct pointers. *)
  method private rewrite_function_type (ret_is_struct, args_are_structs) t =
    let ret, args = Helpers.flatten_arrow t in
    let ret = self#visit_typ [] ret in
    let args = List.map (self#visit_typ []) args in
    let args = List.map2 (fun arg is_struct ->
      if is_struct then
        TBuf (arg, true)
      else
        arg
    ) args args_are_structs in
    let ret, args =
      if ret_is_struct then
        TUnit, args @ [ TBuf (ret, false) ]
      else
        ret, args
    in
    Helpers.fold_arrow args ret

  (* This method rewrites an application node [e args] into [let x = args in e &args]. It
   * exhibits three behaviors.
   * - If the function is not struct-returning, then no further transformations
   *   occur, the type is preserved, and the expression above is returned.
   * - If the function returns a struct, and [dest] is [None], then the function
   *   returns [let dst in let x = e in f &x &dst; dst], thereby preserving the
   *   type [t] of the expression.
   * - If the function returns a struct, and [dest] is [Some dst], then the
   *   function returns [let x = e in f &x &dst], which has type [unit], and it is
   *   up to the caller to wrap this in a way that preserves the type. *)
  method private rewrite_app to_be_starred e args dest =
    let t, _ = Helpers.flatten_arrow e.typ in

    (* Determine using our computed table which of the arguments and the
     * return type must be passed by reference. We could alternatively use
     * the type of [e], but it sometimes may be incomplete. *)
    let ret_is_struct, args_are_structs = analyze_function_type is_struct e.typ in

    (* Partial application. Not Low*... bail. This ensures [t] is the return
     * type of the function call. *)
    if List.length args_are_structs <> List.length args then
      raise NotLowStar;

    (* Ensure things remain well-typed. *)
    let t_rewritten = self#rewrite_function_type (ret_is_struct, args_are_structs) e.typ in
    let e = with_type t_rewritten (self#visit_expr' (to_be_starred, t_rewritten) e.node) in

    (* At call-site, [f e] can only be transformed into [f &e] is [e] is an
     * [lvalue]. This is, sadly, a little bit of an anticipation over the
     * ast-to-C* translation phase. TODO remove the check, and rely on
     * AstToCStar or a Helpers phase to fix this. *)
    let bs, args = KList.fold_lefti (fun i (bs, es) (e, is_struct) ->
      if is_struct then
        if will_be_lvalue e then
          bs, with_type (TBuf (e.typ, true)) (EAddrOf e) :: es
        else
          let x, atom = Helpers.mk_binding (Printf.sprintf "s%d" i) e.typ in
          (x, e) :: bs, with_type (TBuf (e.typ, true)) (EAddrOf atom) :: es
      else
        bs, e :: es
    ) ([], []) (List.combine args args_are_structs) in
    let args = List.rev args in

    (* The three behaviors described above. *)
    if ret_is_struct then
      match dest with
      | Some dest ->
          let args = args @ [ with_type (TBuf (t, false)) (EAddrOf dest) ] in
          Helpers.nest bs t (with_type TUnit (EApp (e, args)))
      | None ->
          let x, dest = Helpers.mk_binding "ret" t in
          let bs = (x, with_type TAny EAny) :: bs in
          let args = args @ [ with_type (TBuf (t, false)) (EAddrOf dest) ] in
          Helpers.nest bs t (with_type t (ESequence [
            with_type TUnit (EApp (e, args));
            dest]))
    else
      Helpers.nest bs t (with_type t (EApp (e, args)))

  method! visit_DFunction _ cc flags n ret lid binders body =
    (* Step 0: parameters at function types get transformed, too. This has no
     * incidence on the result of is_struct. *)
    let binders = self#visit_binders_w [] binders in
    let ret = self#visit_typ [] ret in

    (* Step 1: open all the binders *)
    let binders, body = DeBruijn.open_binders binders body in

    let ret_is_struct = is_struct ret in
    let args_are_structs = List.map (fun x -> is_struct x.typ) binders in

    (* Step 2: rewrite the types of the arguments to take pointers to structs *)
    let binders = List.map2 (fun binder is_struct ->
      if is_struct then
        { binder with typ = TBuf (binder.typ, true) }
      else
        binder
    ) binders args_are_structs in

    (* Step 3: add an extra argument in case the return type is a struct, too *)
    let ret, binders, ret_atom =
      if ret_is_struct then
        let ret_binder, ret_atom = Helpers.mk_binding "ret" (TBuf (ret, false)) in
        TUnit, binders @ [ ret_binder ], Some ret_atom
      else
        ret, binders, None
    in

    (* ... and remember the corresponding atoms: every occurrence becomes a
     * dereference. *)
    let to_be_starred = KList.filter_map (fun (binder, is_struct) ->
      if is_struct then
        Some binder.node.atom
      else
        None
    ) (List.combine binders (args_are_structs @ (if ret_is_struct then [ false ] else []))) in

    let body = self#visit_expr_w to_be_starred body in

    (* Step 4: if the function now takes an extra argument for the output struct. *)
    let body =
      if ret_is_struct then
        with_type TUnit (EBufWrite (Option.must ret_atom, Helpers.zerou32, body))
      else
        body
    in
    let body = DeBruijn.close_binders binders body in
    DFunction (cc, flags, n, ret, lid, binders, body)

  method! visit_TArrow _ t1 t2 =
    let t = TArrow (t1, t2) in
    self#rewrite_function_type (analyze_function_type is_struct t) t

  method! visit_EOpen (to_be_starred, t) name atom =
    (* [x] was a struct parameter that is now passed by reference; replace it
     * with [*x] *)
    if List.exists (Atom.equal atom) to_be_starred then
      EBufRead (with_type (TBuf (t, true)) (EOpen (name, atom)), Helpers.zerou32)
    else
      EOpen (name, atom)

  method! visit_EAssign (to_be_starred, _) e1 e2 =
    let e1 = self#visit_expr_w to_be_starred e1 in
    match e2.node with
    | EApp (e, args) when fst (analyze_function_type is_struct e.typ) ->
        begin try
          let args = List.map (self#visit_expr_w to_be_starred) args in
          assert (will_be_lvalue e1);
          (self#rewrite_app to_be_starred e args (Some e1)).node
        with Not_found | NotLowStar ->
          EAssign (e1, self#visit_expr_w to_be_starred e2)
        end
    | _ ->
        EAssign (e1, self#visit_expr_w to_be_starred e2)

  method! visit_EBufWrite (to_be_starred, _) e1 e2 e3 =
    let e1 = self#visit_expr_w to_be_starred e1 in
    let e2 = self#visit_expr_w to_be_starred e2 in
    match e3.node with
    | EApp (e, args) when fst (analyze_function_type is_struct e.typ) ->
        begin try
          let args = List.map (self#visit_expr_w to_be_starred) args in
          let t = Helpers.assert_tbuf e1.typ in
          let dest = with_type t (EBufRead (e1, e2)) in
          (self#rewrite_app to_be_starred e args (Some dest)).node
        with Not_found | NotLowStar ->
          EBufWrite (e1, e2, self#visit_expr_w to_be_starred e3)
        end
    | _ ->
        EBufWrite (e1, e2, self#visit_expr_w to_be_starred e3)

  method! visit_ELet (to_be_starred, t) b e1 e2 =
    let e2 = self#visit_expr_w to_be_starred e2 in
    match e1.node with
    | EApp (e, args) when fst (analyze_function_type is_struct e.typ) ->
        begin try
          let args = List.map (self#visit_expr_w to_be_starred) args in
          let b, e2 = DeBruijn.open_binder b e2 in
          (* Anticipating on the next phase; marking mut to prevent it from
           * turning into a const pointer (it *is* going to be mutated!) *)
          let b = Helpers.mark_mut b in
          let e1 = self#rewrite_app to_be_starred e args (Some (DeBruijn.term_of_binder b)) in
          ELet (b, Helpers.any, DeBruijn.close_binder b (with_type t (
            ESequence [
              e1;
              e2
            ]
          )))
        with Not_found | NotLowStar ->
          ELet (self#visit_binder_w [] b, self#visit_expr_w to_be_starred e1, e2)
        end
    | _ ->
        ELet (self#visit_binder_w [] b, self#visit_expr_w to_be_starred e1, e2)

  method! visit_EApp (to_be_starred, _) e args =
    let args = List.map (self#visit_expr_w to_be_starred) args in
    begin try
      (self#rewrite_app to_be_starred e args None).node
    with Not_found | NotLowStar ->
      EApp (self#visit_expr_w to_be_starred e, args)
    end

end

let pass_by_ref files =
  let is_struct = mk_is_struct files in
  (pass_by_ref is_struct)#visit_files [] files

let hidden_visibility = {|
#if defined(__GNUC__) && !(defined(_WIN32) || defined(_WIN64))
__attribute__ ((visibility ("hidden")))
#endif
|}

(* Collect static initializers into a separate function, possibly generated by
 * the pass above. *)
let collect_initializers (files: Ast.file list) =
  let initializers = ref [] in
  let record x = initializers := x :: !initializers in
  let files = (object
    inherit [_] map
    method! visit_DGlobal _ flags name n t body =
      let flags, body =
        (* Note: no need to generate a copy-assignment because top-level
         * stack-allocated arrays are not possible in F*. *)
        if not (Helpers.is_initializer_constant body) then begin
          Warn.(maybe_fatal_error ("", NotInitializerConstant (name, body)));
          record (with_type TUnit (EAssign (with_type t (EQualified name), body)));
          List.filter ((<>) Private) flags, with_type t EAny
        end else
          flags, body
      in
      DGlobal (flags, name, n, t, body)
  end)#visit_files () files in
  if !initializers != [] then
    let file = "kremlinit",
      [ DFunction (None, [ Common.Prologue hidden_visibility ], 0, TUnit, (["kremlinit"], "globals"),
        [Helpers.fresh_binder "_" TUnit],
        with_type TUnit (ESequence (List.rev !initializers)))] in
    let files = files @ [ file ] in
    let found = ref false in
    let files = (object
      inherit [_] map
      method! visit_DFunction _ cc flags n ret name binders body =
        let body =
          if GlobalNames.target_c_name ~attempt_shortening:false ~is_macro:false name = "main" then begin
            found := true;
            with_type ret (ESequence [
              with_type TUnit (EApp (
                with_type (TArrow (TUnit, TUnit)) (EQualified ([ "kremlinit" ], "globals")),
                [ Helpers.eunit ]));
              body
            ])
          end else
            body
        in
        DFunction (cc, flags, n, ret, name, binders, body)
    end)#visit_files () files in
    if not !found then
      Warn.(maybe_fatal_error ("", MustCallKrmlInit));
    files
  else
    files


(* Ensure that values of struct types are always allocated at a given address,
 * i.e. in a stack buffer. Specifically, we perform two rewritings, where [t] is
 * a struct type:
 * - [{ f = e }] becomes [let x: t* = ebufcreate { f = e } 1 in *x]
 * - [let x: t = e1 in e2] becomes [let x: t* = &e1 in [x*/x]e2]
 * We also perform a cosmetic rewriting:
 * - [&x[0]] becomes [x].
 *
 * For EBufCreate nodes, we accept literals as an argument, but may hoist things
 * within these literals (see "under_compound").
 *
 * This phase assumes all lets have been hoisted. *)
let to_addr is_struct =
  let rec to_addr under_compound e =
    let was_struct = is_struct e.typ in
    let not_struct () = assert (not was_struct) in
    let w = with_type e.typ in
    let push_addrof e =
      let t = TBuf (e.typ, true) in
      Helpers.nest_in_return_pos t (fun _ e -> with_type t (EAddrOf e)) e
    in
    match e.node with
    | ETApp _ ->
        failwith "should've been eliminated"
    (* Mundane cases. None of these may have a struct type. *)
    | EAny
    | EUnit
    | EBool _
    | EString _
    | EOp _
    | EBreak
    | EConstant _
    | EPushFrame
    | EPopFrame
    | EStandaloneComment _
    | EEnum _ ->
        not_struct ();
        e

    | EQualified _ ->
        if is_struct e.typ then
          Helpers.mk_deref e.typ (EAddrOf e)
        else
          e

    | EAbort _
    | EOpen _ | EBound _ ->
        e

    | EWhile (e1, e2) ->
        not_struct ();
        w (EWhile (to_addr false e1, to_addr false e2))

    | EFor (b, e1, e2, e3, e4) ->
        not_struct ();
        w (EFor (b, to_addr false e1, to_addr false e2, to_addr false e3, to_addr false e4))

    | EIgnore e ->
        not_struct ();
        w (EIgnore (to_addr false e))

    | EApp (e, es) ->
        not_struct ();
        w (EApp (to_addr false e, List.map (to_addr false) es))

    | EFlat fields ->
        if not (was_struct || under_compound && Helpers.is_union e.typ) then
          Warn.fatal_error
            "This was neither a struct or a union field of a struct: %a\n"
            pexpr e;
        let fields = List.map (fun (f, e) -> f, to_addr true e) fields in
        if under_compound then
          w (EFlat fields)
        else
          let b, _ = Helpers.mk_binding "alloc" (TBuf (e.typ, true)) in
          w (ELet (b,
            with_type (TBuf (e.typ, true)) (EBufCreate (Stack, with_type e.typ (EFlat fields), Helpers.oneu32)),
            Helpers.mk_deref e.typ ~const:true (EBound 0)))

    | ELet (b, ({ node = EFlat _; _ } as e1), e2) ->
        (* This special case is subsumed by the combination of [EFlat] and
         * [ELet], but generates un-necessary names, and complicates debugging.
         * *)
        if not (is_struct b.typ) then
          Warn.fatal_error "%a is not a struct type\n" ptyp b.typ;
        let t = b.typ in
        let const = not b.node.mut in
        let t' = TBuf (b.typ, const) in
        let b = { b with typ = t' } in
        let e1 = to_addr true e1 in
        let e1 = with_type t' (EBufCreate (Stack, e1, Helpers.oneu32)) in
        let e2 = DeBruijn.subst_no_open (Helpers.mk_deref t ~const (EBound 0)) 0 e2 in
        w (ELet (b, e1, to_addr false e2))

    | ELet (b, e1, e2) ->
        let b, e1, e2 =
          if is_struct b.typ then
            (* Our transformation kicks in. *)
            let const = not b.node.mut in
            let t' = TBuf (b.typ, const) in
            let e1 =
              if e1.node = EAny then
                (* [let x: t = any] becomes [let x: t* = ebufcreate any 1] *)
                with_type t' (EBufCreate (Stack, e1, Helpers.oneu32))
              else
                (* Recursively visit [e1]; take the resulting address. *)
                push_addrof (to_addr false e1)
            in
            { b with typ = t' },
            e1,
            DeBruijn.subst_no_open
              (Helpers.mk_deref b.typ ~const (EBound 0))
              0
              e2
          else
            b, to_addr false e1, e2
        in
        let e2 = to_addr false e2 in
        w (ELet (b, e1, e2))

    | EIfThenElse (e1, e2, e3) ->
        w (EIfThenElse (to_addr false e1, to_addr false e2, to_addr false e3))

    | EAssign (e1, e2) ->
        (* In the case of a by-copy struct assignment (for the return value of
         * an if-then-else, for instance), we do not recurse. This is morally an
         * EBufFill. *)
        not_struct ();
        let e1 = to_addr false e1 in
        if is_struct e1.typ then
          let e2 = to_addr false e2 in
          match e1.node with
          | EBufRead (e0, e1) ->
              w (EBufWrite (e0, e1, e2))
          | _ ->
              Warn.fatal_error "not an ebufread: %a\n" pexpr e1
        else
          w (EAssign (e1, e2))

    | EBufCreate (l, e1, e2) ->
        let e2 = to_addr false e2 in
        w (EBufCreate (l, e1, e2))

    | EBufCreateL _ ->
        e

    | EBufRead (e1, e2) ->
        w (EBufRead (to_addr false e1, to_addr false e2))

    | EBufWrite (e1, e2, e3) ->
        not_struct ();
        let e1 = to_addr false e1 in
        let e2 = to_addr false e2 in
        let e3 = to_addr false e3 in
        w (EBufWrite (e1, e2, e3))

    | EField (e, f) ->
        w (EField (to_addr false e, f))

    | EAddrOf e ->
        w (EAddrOf (to_addr false e))

    | EBufSub (e1, e2) ->
        w (EBufSub (e1, e2))

    | EBufBlit (e1, e2, e3, e4, e5) ->
        w (EBufBlit (to_addr false e1, to_addr false e2, to_addr false e3, to_addr false e4, to_addr false e5))

    | EBufFill (e1, e2, e3) ->
        (* Not descending into e2 *)
        let e1 = to_addr false e1 in
        let e3 = to_addr false e3 in
        w (EBufFill (e1, e2, e3))

    | EBufFree e ->
        (* Not descending, this is already an address *)
        w (EBufFree e)

    | ESwitch (e, branches) ->
        let e = to_addr false e in
        let branches = List.map (fun (lid, e) -> lid, to_addr false e) branches in
        w (ESwitch (e, branches))

    | EReturn e ->
        assert (not (is_struct e.typ));
        w (EReturn (to_addr false e))

    | ECast (e, t) ->
        w (ECast (to_addr false e, t))

    | EComment (s, e, s') ->
        w (EComment (s, to_addr false e, s'))

    | ESequence _
    | ETuple _
    | EMatch _
    | ECons _
    | EFun _ ->
        Warn.fatal_error "impossible: %a" pexpr e
  in
  object
    inherit [_] map

    method! visit_DFunction _ cc flags n ret lid binders body =
      DFunction (cc, flags, n, ret, lid, binders, to_addr false body)
  end


(* For C89 *)
let remove_literals = object (self)
  inherit [_] map as super

  method private mk_path (e: expr) (t: typ) (fields: ident list) =
    List.fold_left (fun acc f -> with_type t (EField (acc, f))) e fields

  method private explode (acc: expr list) (path: ident list) (e: expr) (dst: expr) =
    match e.node with
    | EFlat fields ->
        List.fold_left (fun acc (f, e) ->
          let f = Option.must f in
          self#explode acc (f :: path) e dst
        ) acc fields
    | _ ->
        let e = self#visit_expr_w () e in
        with_type TUnit (EAssign (self#mk_path dst e.typ (List.rev path), e)) :: acc

  method! visit_ELet ((_, t) as env) b e1 e2 =
    match e1.node with
    | EFlat fields ->
        let fields = List.map (fun (f, e) -> f, DeBruijn.lift 1 e) fields in
        let x = with_type b.typ (EBound 0) in
        ELet (b, Helpers.any, with_type t (ESequence (
          List.rev (self#visit_expr_w () e2 ::
            self#explode [] [] (with_type e1.typ (EFlat fields)) x))))
    | _ ->
        super#visit_ELet env b e1 e2

  method! visit_EFlat (_, t) fields =
    let b, x = Helpers.mk_binding "lit" t in
    ELet (b, Helpers.any, DeBruijn.close_binder b (with_type t (ESequence (
      List.rev (x :: self#explode [] [] (with_type t (EFlat fields)) x)))))

  method visit_fields_t_opt _ fields =
    (* All fields become mutable with this transformation *)
    List.map (fun (f, (t, _)) -> f, (self#visit_typ () t, true)) fields
end

let remove_literals files =
  remove_literals#visit_files () files

(* Debug any intermediary AST as follows: *)
(* PPrint.(Print.(print (PrintAst.print_files files ^^ hardline))); *)

let in_memory files =
  (* TODO: do let_to_sequence and sequence_to_let once! *)
  let is_struct = mk_is_struct files in
  let files = (to_addr is_struct)#visit_files () files in
  files

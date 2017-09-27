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
          false
        end
    | _ ->
        false

(* Construct a [lid -> bool * bool list]; the first component tells whether
 * the return value of the function should be caller-allocated and passed as the
 * last parameter to the function; the second component tells, for each
 * parameter of the function, whether it has a struct type. *)
let mk_action_table files =
  let is_struct = mk_is_struct files in
  let map = Hashtbl.create 41 in
  List.iter (fun (_, decls) ->
    List.iter (function
      | DFunction (_, _, _, ret, lid, binders, _body) ->
          Hashtbl.add map lid (is_struct ret, List.map (fun b -> is_struct b.typ) binders)
      | DExternal (_, lid, typ) ->
          begin match typ with
          | TArrow _ ->
              let ret, args = Helpers.flatten_arrow typ in
              Hashtbl.add map lid (is_struct ret, List.map is_struct args)
          | _ ->
              ()
          end
      | _ ->
          ()
    ) decls
  ) files;
  map

(* Rewrite a function type to take and possibly return struct pointers. *)
let rewrite_function_type (ret_is_struct, args_are_structs) t =
  let ret, args = Helpers.flatten_arrow t in
  let args = List.map2 (fun arg is_struct ->
    if is_struct then
      TBuf arg
    else
      arg
  ) args args_are_structs in
  let ret, args =
    if ret_is_struct then
      TUnit, args @ [ TBuf ret ]
    else
      ret, args
  in
  Helpers.fold_arrow args ret

let will_be_lvalue e =
  match e.node with
  | EBound _ | EOpen _ | EBufRead _ ->
      true
  | _ ->
      false

exception NotLowStar

(* This function rewrites an application node [e args] into [let x = args in e &args]. It
 * exhibits three behaviors.
 * - If the function is not struct-returning, then no further transformations
 *   occur, the type is preserved, and the expression above is returned.
 * - If the function returns a struct, and [dest] is [None], then the function
 *   returns [let dst in let x = e in f &x &dst; dst], thereby preserving the
 *   type [t] of the expression.
 * - If the function returns a struct, and [dest] is [Some dst], then the
 *   function returns [let x = e in f &x &dst], which has type [unit], and it is
 *   up to the caller to wrap this in a way that preserves the type. *)
let rewrite_app action_table e args dest =
  let lid = Helpers.assert_elid e.node in
  let t, _ = Helpers.flatten_arrow e.typ in

  (* Determine using our computed table which of the arguments and the
   * return type must be passed by reference. We could alternatively use
   * the type of [e], but it sometimes may be incomplete. *)
  let ret_is_struct, args_are_structs = Hashtbl.find action_table lid in

  (* Partial application. Not Low*... bail. This ensures [t] is the return
   * type of the function call. *)
  if List.length args_are_structs <> List.length args then
    raise NotLowStar;

  (* Ensure things remain well-typed. *)
  let e = with_type (rewrite_function_type (ret_is_struct, args_are_structs) e.typ) (EQualified lid) in

  (* At call-site, [f e] can only be transformed into [f &e] is [e] is an
   * [lvalue]. This is, sadly, a little bit of an anticipation over the
   * ast-to-C* translation phase. TODO remove the check, and rely on
   * AstToCStar or a Helpers phase to fix this. *)
  let bs, args = KList.fold_lefti (fun i (bs, es) (e, is_struct) ->
    if is_struct then
      if will_be_lvalue e then
        bs, with_type (TBuf e.typ) (EAddrOf e) :: es
      else
        let x, atom = Helpers.mk_binding (Printf.sprintf "s%d" i) e.typ in
        (x, e) :: bs, with_type (TBuf e.typ) (EAddrOf atom) :: es
    else
      bs, e :: es
  ) ([], []) (List.combine args args_are_structs) in
  let args = List.rev args in

  (* The three behaviors described above. *)
  if ret_is_struct then
    match dest with
    | Some dest ->
        let args = args @ [ with_type (TBuf t) (EAddrOf dest) ] in
        Helpers.nest bs t (with_type TUnit (EApp (e, args)))
    | None ->
        let x, dest = Helpers.mk_binding "ret" t in
        let bs = (x, with_type TAny EAny) :: bs in
        let args = args @ [ with_type (TBuf t) (EAddrOf dest) ] in
        Helpers.nest bs t (with_type t (ESequence [
          with_type TUnit (EApp (e, args));
          dest]))
  else
    Helpers.nest bs t (with_type t (EApp (e, args)))

(* Rewrite functions and expressions to take and possibly return struct
 * pointers. *)
let pass_by_ref action_table = object (self)

  (* We open all the parameters of a function; then, we pass down as the
   * environment the list of atoms that correspond to by-ref parameters. These
   * will have to be "starred". *)
  inherit [Atom.t list] map

  method! dfunction _ cc flags n ret lid binders body =
    (* Step 1: open all the binders *)
    let binders, body = DeBruijn.open_binders binders body in

    let ret_is_struct, args_are_structs = Hashtbl.find action_table lid in

    (* Step 2: rewrite the types of the arguments to take pointers to structs *)
    let binders = List.map2 (fun binder is_struct ->
      if is_struct then
        { binder with typ = TBuf binder.typ }
      else
        binder
    ) binders args_are_structs in

    (* Step 3: add an extra argument in case the return type is a struct, too *)
    let ret, binders, ret_atom =
      if ret_is_struct then
        let ret_binder, ret_atom = Helpers.mk_binding "ret" (TBuf ret) in
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

    let body = self#visit to_be_starred body in

    (* Step 4: if the function now takes an extra argument for the output struct. *)
    let body =
      if ret_is_struct then
        with_type TUnit (EBufWrite (Option.must ret_atom, Helpers.zerou32, body))
      else
        body
    in
    let body = DeBruijn.close_binders binders body in
    DFunction (cc, flags, n, ret, lid, binders, body)

  method dexternal _ cc lid t =
    match t with
    | TArrow _ ->
        (* Also rewrite external function declarations. *)
        let ret, args = Helpers.flatten_arrow t in
        let ret_is_struct, args_are_structs = Hashtbl.find action_table lid in
        let buf_if arg is_struct = if is_struct then TBuf arg else arg in
        let ret, args =
          if ret_is_struct then
            TUnit, List.map2 buf_if args args_are_structs @ [ TBuf ret ]
          else
            ret, List.map2 buf_if args args_are_structs
        in
        DExternal (cc, lid, Helpers.fold_arrow args ret)
    | _ ->
        DExternal (cc, lid, t)


  method! eopen to_be_starred t name atom =
    (* [x] was a strut parameter that is now passed by reference; replace it
     * with [*x] *)
    if List.exists (Atom.equal atom) to_be_starred then
      EBufRead (with_type (TBuf t) (EOpen (name, atom)), Helpers.zerou32)
    else
      EOpen (name, atom)

  method! eassign to_be_starred _ e1 e2 =
    let e1 = self#visit to_be_starred e1 in
    match e2.node with
    | EApp ({ node = EQualified lid; _ } as e, args) when
      try fst (Hashtbl.find action_table lid) with Not_found -> false ->
        begin try
          let args = List.map (self#visit to_be_starred) args in
          assert (will_be_lvalue e1);
          (rewrite_app action_table e args (Some e1)).node
        with Not_found | NotLowStar ->
          EAssign (e1, self#visit to_be_starred e2)
        end
    | _ ->
        EAssign (e1, self#visit to_be_starred e2)

  method! ebufwrite to_be_starred _ e1 e2 e3 =
    let e1 = self#visit to_be_starred e1 in
    let e2 = self#visit to_be_starred e2 in
    match e3.node with
    | EApp ({ node = EQualified lid; _ } as e, args) when
      try fst (Hashtbl.find action_table lid) with Not_found -> false ->
        begin try
          let args = List.map (self#visit to_be_starred) args in
          let t = Helpers.assert_tbuf e1.typ in
          let dest = with_type t (EBufRead (e1, e2)) in
          (rewrite_app action_table e args (Some dest)).node
        with Not_found | NotLowStar ->
          EBufWrite (e1, e2, self#visit to_be_starred e3)
        end
    | _ ->
        EBufWrite (e1, e2, self#visit to_be_starred e3)

  method! elet to_be_starred t b e1 e2 =
    let e2 = self#visit to_be_starred e2 in
    match e1.node with
    | EApp ({ node = EQualified lid; _ } as e, args) when
      try fst (Hashtbl.find action_table lid) with Not_found -> false ->
        begin try
          let args = List.map (self#visit to_be_starred) args in
          let b, e2 = DeBruijn.open_binder b e2 in
          let e1 = rewrite_app action_table e args (Some (DeBruijn.term_of_binder b)) in
          ELet (b, Helpers.any, DeBruijn.close_binder b (with_type t (
            ESequence [
              e1;
              e2
            ]
          )))
        with Not_found | NotLowStar ->
          ELet (b, self#visit to_be_starred e1, e2)
        end
    | _ ->
        ELet (b, self#visit to_be_starred e1, e2)

  method! eapp to_be_starred _ e args =
    let args = List.map (self#visit to_be_starred) args in
    match e.node with
    | EQualified _ ->
        begin try
          (rewrite_app action_table e args None).node
        with Not_found | NotLowStar ->
          EApp (e, args)
        end
    | _ ->
        EApp (e, args)

end

let pass_by_ref files =
  let action_table = mk_action_table files in
  Helpers.visit_files [] (pass_by_ref action_table) files


(* Collect static initializers into a separate function, possibly generated by
 * the pass above. *)
let collect_initializers (files: Ast.file list) =
  let initializers = ref [] in
  let record x = initializers := x :: !initializers in
  let files = Helpers.visit_files () (object
    inherit [unit] map
    method dglobal _ flags name t body =
      let flags, body =
        if not (Helpers.is_value body) then begin
          record (with_type TUnit (EAssign (with_type t (EQualified name), body)));
          List.filter ((<>) Private) flags, with_type t EAny
        end else
          flags, body
      in
      DGlobal (flags, name, t, body)
  end) files in
  if !initializers != [] then
    let file = "kremlinit",
      [ DFunction (None, [], 0, TUnit, (["kremlinit"], "globals"),
        [Helpers.fresh_binder "_" TUnit],
        with_type TUnit (ESequence (List.rev !initializers)))] in
    let files = files @ [ file ] in
    let found = ref false in
    let files = Helpers.visit_files () (object
      inherit [unit] map
      method dfunction _ cc flags n ret name binders body =
        let body =
          if Simplify.target_c_name name = "main" then begin
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
    end) files in
    if not !found then
      Warnings.(maybe_fatal_error ("", MustCallKrmlInit));
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
 * We do not recurse into the initial value of ebufcreate nodes, the rhs of
 * ebufwrite, and into nested structs within outer struct literals. All of these
 * already have a destination address, meaning the WASM codegen will be able to
 * handle them.
 *
 * This phase assumes all lets have been hoisted. *)
let to_addr is_struct =
  let rec to_addr e =
    let was_struct = is_struct e.typ in
    let not_struct () = assert (not was_struct) in
    let w = with_type e.typ in
    let push_addrof e =
      let t = TBuf e.typ in
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
        w (EWhile (to_addr e1, to_addr e2))

    | EFor (b, e1, e2, e3, e4) ->
        not_struct ();
        w (EFor (b, to_addr e1, to_addr e2, to_addr e3, to_addr e4))

    | EIgnore e ->
        not_struct ();
        w (EIgnore (to_addr e))

    | EApp (e, es) ->
        not_struct ();
        w (EApp (to_addr e, List.map to_addr es))

    | EFlat _ ->
        (* Not descending *)
        assert was_struct;
        let b, _ = Helpers.mk_binding "alloc" (TBuf e.typ) in
        w (ELet (b,
          with_type (TBuf e.typ) (EBufCreate (Stack, e, Helpers.oneu32)),
          Helpers.mk_deref e.typ (EBound 0)))

    | ELet (b, ({ node = EFlat _; _ } as e1), e2) ->
        (* This special case is subsumed by the combination of [EFlat] and
         * [ELet], but generates un-necessary names, and complicates debugging.
         * *)
        assert (is_struct b.typ);
        let t = b.typ in
        let t' = TBuf b.typ in
        let b = { b with typ = t' } in
        let e1 = with_type t' (EBufCreate (Stack, e1, Helpers.oneu32)) in
        let e2 = DeBruijn.subst_no_open (Helpers.mk_deref t (EBound 0)) 0 e2 in
        w (ELet (b, e1, to_addr e2))

    | ELet (b, e1, e2) ->
        let b, e1, e2 =
          if is_struct b.typ then
            (* Our transformation kicks in. *)
            let t' = TBuf b.typ in
            let e1 =
              if e1.node = EAny then
                (* [let x: t = any] becomes [let x: t* = ebufcreate any 1] *)
                with_type (TBuf b.typ) (EBufCreate (Stack, e1, Helpers.oneu32))
              else
                (* Recursively visit [e1]; take the resulting address. *)
                push_addrof (to_addr e1)
            in
            { b with typ = t' },
            e1,
            DeBruijn.subst_no_open
              (Helpers.mk_deref b.typ (EBound 0))
              0
              e2
          else
            b, to_addr e1, e2
        in
        let e2 = to_addr e2 in
        w (ELet (b, e1, e2))

    | EIfThenElse (e1, e2, e3) ->
        w (EIfThenElse (to_addr e1, to_addr e2, to_addr e3))

    | EAssign (e1, e2) ->
        (* In the case of a by-copy struct assignment (for the return value of
         * an if-then-else, for instance), we do not recurse. This is morally an
         * EBufFill. *)
        not_struct ();
        let e1 = to_addr e1 in
        let e2 = if is_struct e1.typ then e2 else to_addr e2 in
        w (EAssign (e1, e2))

    | EBufCreate (l, e1, e2) ->
        (* Not descending into [e1], as it will undergo the "allocate at
         * address" treatment later on *)
        let e2 = to_addr e2 in
        w (EBufCreate (l, e1, e2))

    | EBufCreateL _ ->
        e

    | EBufRead (e1, e2) ->
        w (EBufRead (to_addr e1, to_addr e2))

    | EBufWrite (e1, e2, e3) ->
        (* Not descending into [e3]... *)
        not_struct ();
        let e1 = to_addr e1 in
        let e2 = to_addr e2 in
        w (EBufWrite (e1, e2, e3))

    | EField (e, f) ->
        w (EField (to_addr e, f))

    | EAddrOf e ->
        w (EAddrOf (to_addr e))

    | EBufSub (e1, e2) ->
        w (EBufSub (e1, e2))

    | EBufBlit (e1, e2, e3, e4, e5) ->
        w (EBufBlit (to_addr e1, to_addr e2, to_addr e3, to_addr e4, to_addr e5))

    | EBufFill (e1, e2, e3) ->
        (* Not descending into e2 *)
        let e1 = to_addr e1 in
        let e3 = to_addr e3 in
        w (EBufFill (e1, e2, e3))

    | ESwitch (e, branches) ->
        let e = to_addr e in
        let branches = List.map (fun (lid, e) -> lid, to_addr e) branches in
        w (ESwitch (e, branches))

    | EReturn e ->
        assert (not (is_struct e.typ));
        w (EReturn (to_addr e))

    | ECast (e, t) ->
        w (ECast (to_addr e, t))

    | EComment (s, e, s') ->
        w (EComment (s, to_addr e, s'))

    | ESequence _
    | ETuple _
    | EMatch _
    | ECons _
    | EFun _ ->
        Warnings.fatal_error "impossible: %a" pexpr e
  in
  object (_self)
    inherit [unit] map

    method! dfunction _ cc flags n ret lid binders body =
      DFunction (cc, flags, n, ret, lid, binders, to_addr body)
  end


let in_memory files =
  (* TODO: do let_to_sequence and sequence_to_let once! *)
  let is_struct = mk_is_struct files in
  let files = Helpers.visit_files () Simplify.sequence_to_let files in
  let files = Helpers.visit_files () (to_addr is_struct) files in
  let files = Helpers.visit_files () Simplify.let_to_sequence files in
  files

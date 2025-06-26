(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 and MIT Licenses. *)

(** Whole-program inlining based on the [MustDisappear] flag passed by F*. *)

module LidSet = Idents.LidSet

open Ast
open PrintAst.Ops
open Common

(* Natural arity analysis must be performed before inlining (see comment in
 * [inline_one]. *)
let natural_arity = Hashtbl.create 43

let compute_natural_arity = object
  inherit [_] iter

  method! visit_DFunction () _ _ _ _ _ name args _ =
    Hashtbl.add natural_arity name (List.length args)
end

let rec flatten_app e =
  match e.node with
  | EApp (e, es) ->
      let e, es' = flatten_app e in
      e, es' @ es
  | _ ->
      e, []

let reparenthesize_applications = object (self)
  inherit [_] map

  method! visit_EApp (_, t as env) e es =
    let e, es = flatten_app (with_type t (EApp (e, es))) in
    let es = List.map (self#visit_expr env) es in
    let e = self#visit_expr env e in
    match e.node with
    | EQualified lid | ETApp ({ node = EQualified lid; _ }, _, _, _) ->
        begin try
          let n = Hashtbl.find natural_arity lid in
          let first, last = KList.split n es in
          let app1 = with_type t (EApp (e, first)) in
          if List.length last > 0 then
            EApp (app1, last)
          else
            app1.node
        with
          | Not_found ->
              if Options.debug "arity" then
                KPrint.bprintf "Cannot enforce arity at call-site for %a because it is not in scope (assume val?)\n" plid lid;
              EApp (e, es)
          | Invalid_argument s ->
              Warn.maybe_fatal_error ("", Arity (lid,
                KPrint.bsprintf "Invalid_argument %s -- is this a partial application?" s));
              EApp (e, es)
        end
    | _ ->
        if Options.debug "arity" then
          KPrint.bprintf "Cannot enforce arity at call-site for %a (not an lid)\n" pexpr e;
        EApp (e, es)
end

let reparenthesize_applications files =
  compute_natural_arity#visit_files () files;
  let files = reparenthesize_applications#visit_files () files in
  files

(* Inlining of function bodies ************************************************)

(** We rely on the textbook three-color graph traversal; inlining cycles are a
 * hard error. *)
type color = White | Gray | Black

(* A generic graph traversal + memoization combinator we use for inline
 * functions and types. *)
let rec memoize_inline map visit lid =
  let color, body = Hashtbl.find map lid in
  match color with
  | Gray ->
      Warn.fatal_error "[Frames]: cyclic dependency on %a" plid lid
  | Black ->
      body
  | White ->
      Hashtbl.replace map lid (Gray, body);
      let body = visit (memoize_inline map visit) body in
      Hashtbl.replace map lid (Black, body);
      body

(** For a given set of files, and a criterion that maps each function [lid] to a
 * boolean, return a function from an [lid] to its body where inlining has been
 * performed. *)
let mk_inliner files criterion =
  (* Build a map suitable for the [memoize_inline] combinator. *)
  let map = Helpers.build_map files (fun map -> function
    | DGlobal (_, name, _, _, body)
    | DFunction (_, _, _, _, _, name, _, body) ->
        Hashtbl.add map name (White, body)
    | _ ->
        ()
  ) in
  let inline_one = memoize_inline map (fun recurse -> (object(self)
    inherit [_] map
    method! visit_EApp (_, t) e es =
      let es = List.map (self#visit_expr_w ()) es in
      match e.node with
      | EQualified lid when Hashtbl.mem map lid && criterion lid ->
          (* Note: because we don't have the "natural" arity of `lid`, i.e. we
           * don't know how many parameters the function _definition_ takes,
           * meaning we may pass more arguments to safe_substitution than the
           * function definition takes. Safe_substitution just drops them and
           * this results in typing errors later on. *)
          (Helpers.safe_substitution es (recurse lid) t).node
      | _ ->
          EApp (self#visit_expr_w () e, es)
    method! visit_EQualified (_, t) lid =
      match t with
      | TArrow _ when Hashtbl.mem map lid && criterion lid ->
          Warn.fatal_error "[Frames]: %a partially applied function; not meant to happen" plid lid
      | _ ->
          EQualified lid
  end)#visit_expr_w ()) in
  inline_one

(** Relying on the MustDisappear flag passed by F* ****************************)

let inline_analysis files =
  let map = Helpers.build_map files (fun map -> function
    | DGlobal (flags, name, _, _, body)
    | DFunction (_, flags, _, _, _, name, _, body) ->
        Hashtbl.add map name (White, flags, 0, body)
    | _ ->
        ()
  ) in
  let module T = struct exception Cycle end in
  let rec compute_size lid =
    match Hashtbl.find map lid with
    | Gray, _, _, _ ->
        raise T.Cycle
    | Black, _, size, _ ->
        size
    | White, flags, size, body ->
        assert (size = 0);
        Hashtbl.replace map lid (Gray, flags, size, body);
        let visit = object
          inherit [_] reduce
          method! visit_typ _ _ = 0
          method zero = 0
          method plus x y = x + y + 1
          method! visit_EQualified _ lid =
            if Hashtbl.mem map lid then
              compute_size lid
            else
              0
        end in
        let size = visit#visit_expr_w () body in
        Hashtbl.replace map lid (Black, flags, size, body);
        size
  in
  let small_enough lid =
    try
      let size = compute_size lid in
      (* 0 encodes a cycle meaning we shouldn't inline the function *)
      let small = 0 < size && size < 1000 in
      small
    with T.Cycle ->
      let _, flags, _, body = Hashtbl.find map lid in
      Hashtbl.replace map lid (Black, flags, 0, body);
      false
  in
  Hashtbl.add map ([ "krmlinit" ], "globals") (Black, [], 0, Helpers.any);
  let must_disappear lid =
    let _, flags, _, _ = Hashtbl.find map lid in
    List.mem MustDisappear flags
  in
  let must_inline lid =
    let _, flags, _, _ = Hashtbl.find map lid in
    (Options.wasm () && small_enough lid) ||
    List.mem Substitute flags ||
    must_disappear lid
  in
  must_inline, must_disappear

module StringMap = Map.Make(String)

(* After bundling, map filenames to crates *)
let mk_crate_of files =
  let map =
    List.fold_left (fun map (file, _) ->
      StringMap.add file (List.find_map (fun (crate, members, _) ->
        let crate = KList.one (KList.one crate) in
        if List.exists (fun p -> Bundle.pattern_matches_file p file) members then begin
          KPrint.bprintf "File %s goes into crate %s\n" file crate;
          Some crate
        end else
          None
      ) (List.rev !Options.crates)) map
    ) StringMap.empty files
  in
  fun f -> 
    StringMap.find f map

(** This phase is concerned with three whole-program, cross-compilation-unit
    analyses, performed in a single pass:
    - assign correct visibility to declarations in the presence of bundling,
      static-header, mutually-recursive definitions, stackinline,
      inline_for_extraction, the friend mechanism, and the krmlinit_globals
      initializer, all of which force some symbols to become visible
    - strip incorrect inline annotations
    - generate proper wasm mutable getters
*)
let cross_call_analysis files =

  let file_of = Bundle.mk_file_of files in
  let crate_of = mk_crate_of files in

  let module T = struct
    type visibility = Private | Internal | Workspace | Public
    type inlining = Nope | Inline | StaticInline
    type info = {
      visibility: visibility;
      callers: LidSet.t;
      inlining: inlining;
      wasm_mutable: bool;
      wasm_needs_getter: bool;
      abstract_struct: bool;
    }
  end in
  let open T in

  let pvis b = function
    | Private -> Buffer.add_string b "Private"
    | Internal -> Buffer.add_string b "Internal"
    | Public -> Buffer.add_string b "Public"
    | Workspace -> Buffer.add_string b "Workspace"
  in

  (* We associate to each declaration some initial information. Three fields may
     change after initially filling the map:
     - visibility may go upward along the visibility lattice (this is only a
       LOWER bound, not the actual final visibility which needs a fixpoint
       computation)
     - inlining may be downgraded from Inline to Nope
     - the flag wasm_needs_getter might be set
     - the callers are recorded for the purposes of the fixpoint computation *)
  let info_map = Helpers.build_map files (fun map d ->
    let f = flags_of_decl d in
    let name = lid_of_decl d in
    let abstract_struct = List.mem Common.AbstractStruct f in
    let visibility =
      if List.mem Common.Internal f || abstract_struct then
        (* C abstract structs start at internal, since their body is going to be in the internal
           header. *)
        Internal
      else if List.mem Common.Private f then
        Private
      else
        Public
    in
    if Options.debug "visibility-fixpoint" then
      KPrint.bprintf "[initial visibility] %a: %a\n" plid name pvis visibility;
    let inlining =
      let is_static_inline = Helpers.is_static_header name in
      let is_inline = List.mem Common.Inline f || List.mem Common.MustInline f in
      if is_static_inline && is_inline then
        Warn.maybe_fatal_error ("", InlineStaticInline (lid_of_decl d));
      if is_static_inline then
        StaticInline
      else if is_inline then
        Inline
      else
        Nope
    in
    let wasm_mutable =
      match d with
      | DGlobal (_, _, _, (TBuf _ | TArray _), _) ->
          if Options.debug "visibility-fixpoint" then
            KPrint.bprintf "[wasm_mutable]: marking %a\n" plid (lid_of_decl d);
          true
      | _ ->
          false
    in
    let wasm_needs_getter = false in
    let callers = LidSet.empty in
    Hashtbl.add map (lid_of_decl d) { visibility; inlining; wasm_mutable; wasm_needs_getter; callers; abstract_struct }
  ) in

  (* We keep track of the declarations we have seen so far. Since the
     declarations are quasi-topologically ordered, a forward reference to
     another function indicates that there is mutual recursion. *)
  let seen = ref LidSet.empty in

  (* T.Visibility forms a trivial lattice where Private <= Internal <= Public *)
  let lub: visibility -> visibility -> visibility = max in

  (* Set a lower a bound on the visibility of `lid`. *)
  let raise lid v =
    try
      let info = Hashtbl.find info_map lid in
      Hashtbl.replace info_map lid { info with visibility = lub v info.visibility }
    with Not_found ->
      (* External type currently modeled as an lid without a definition (sigh) *)
      ()
  in

  (* Record a call from `caller` to `callee` *)
  let record_call_from_to caller callee =
    try
      let info = Hashtbl.find info_map callee in
      if Options.debug "visibility-fixpoint" then
        KPrint.bprintf "[visibility-fixpoint] recording cross-call from %a (%s) to %a (%s)\n"
          plid caller (Option.value ~default:"<none>" (file_of caller))
          plid callee (Option.value ~default:"<none>" (file_of callee));
      Hashtbl.replace info_map callee { info with callers = LidSet.add caller info.callers }
    with Not_found ->
      (* External type currently modeled as an lid without a definition (sigh) *)
      ()
  in

  (* Is this a call across crate within the same workspace? *)
  let cross_crate name1 name2 =
    let file1 = file_of name1 in
    let file2 = file_of name2 in
    let crate1 = Option.bind file1 crate_of in
    let crate2 = Option.bind file2 crate_of in
    let should_drop = function
      | Some f -> Drop.file f
      | None -> false
    in
    let r = crate1 <> None && crate2 <> None && crate1 <> crate2 && not (should_drop file1 || should_drop file2) in
    if r && Options.debug "visibility-fixpoint" then
      KPrint.bprintf "[visibility-fixpoint] cross-crate from %a (%s) to %a (%s)\n"
        plid name1 (Option.value ~default:"<none>" crate1)
        plid name2 (Option.value ~default:"<none>" crate2);
    r
  in

  (* Is this a call across compilation units? *)
  let cross_call name1 name2 =
    let file1 = file_of name1 in
    let file2 = file_of name2 in
    let should_drop = function
      | Some f -> Drop.file f
      | None -> false
    in
    let r = file1 <> file2 && not (should_drop file1 || should_drop file2) in
    if r && Options.debug "visibility-fixpoint" then
      KPrint.bprintf "[visibility-fixpoint] cross-call from %a (%s) to %a (%s)\n"
        plid name1 (Option.value ~default:"<none>" file1)
        plid name2 (Option.value ~default:"<none>" file2);
    r
  in

  (* First, collect information in the info map. Side-effect: downgrade inlining
     qualifiers. *)
  List.iter (fun (_, decls) ->
    List.iter (fun (d: decl) ->
      let lid = lid_of_decl d in
      let my_info = Hashtbl.find info_map lid in

      (* if `lid` calls into `name` across translation units, then `name` must
         lose its inline qualifier, if any *)
      let maybe_strip_inline name =
        try
          let info = Hashtbl.find info_map name in
          if info.inlining = Inline then begin
            Warn.maybe_fatal_error ("", LostInline (file_of lid, lid, file_of name, name));
            Hashtbl.replace info_map name { info with inlining = Nope }
          end
        with Not_found ->
          if Options.debug "visibility-fixpoint" then
            KPrint.bprintf "[maybe_strip_inline]: definition not found %a\n" plid name
      in

      (* if `lid` refers to `name` across translation units, then `name` needs a
         getter in WASM *)
      let maybe_needs_getter name =
        try
          let info = Hashtbl.find info_map name in
          if info.wasm_mutable then begin
            if Options.debug "visibility-fixpoint" && not info.wasm_needs_getter then
              KPrint.bprintf "%a accesses %a, a mutable global, across modules: getter \
                must be generated\n" plid lid plid name;
            Hashtbl.replace info_map name { info with wasm_needs_getter = true }
          end
        with Not_found ->
          if Options.debug "visibility-fixpoint" then
            KPrint.bprintf "[maybe_needs_getter]: definition not found %a\n" plid name
      in

      let rec visit lid in_body = object (self)
        inherit [_] iter as super

        method! visit_TQualified () name =
          (* Cross-compilation-unit reference to `name`, a type that we need in
             scope for this definition to compile. *)
          if cross_call lid name then
            raise name Internal;
          (* Using the multiple-crate, workspace feature of Rust code-gen. This
             is a call across crates belonging to the same workspace -- the
             definition needs to be visible across the whole workspace. *)
          if cross_crate lid name && !Options.crates <> [] then
            raise name Workspace;
          (* Types that appear in prototypes (i.e., `not in_body`) must be
             raised to the level of visibility of the current definition.
             Types that appear in static inline function definitions (lhs of the
             disjunction) must, in addition to the criterion above, follow
             the same rules as for a prototype. *)
          if in_body && my_info.inlining = StaticInline || not in_body then
            record_call_from_to lid name

        method! visit_TApp () name ts =
          match Hashtbl.find_opt MonomorphizationState.state (name, ts, []) with
          | Some (_, lid, _) ->
              self#visit_TQualified () lid
          | None ->
              self#visit_TQualified () name;
              List.iter (self#visit_typ ()) ts

        method! visit_TTuple () ts =
          match Hashtbl.find_opt MonomorphizationState.state (tuple_lid, ts, []) with
          | Some (_, lid, _) ->
              self#visit_TQualified () lid
          | None ->
              super#visit_TTuple () ts

        method! visit_TCgApp () name ts =
          match Hashtbl.find_opt MonomorphizationState.state (flatten_tapp (TCgApp (name, ts))) with
          | Some (_, lid, _) ->
              self#visit_TQualified () lid
          | None ->
              super#visit_TCgApp () name ts

        method! visit_ETApp ((), t) e _ _ ts =
          (* Monomorphization happened long ago. If we hit this, this means we are the call-site for
             a type- or cg-polymorphic external function. The callee retains its original
             polymorphic signature (e.g. \0. () -> uint8[0] * uint8[0]), and the call-site (here)
             provides the arguments (e.g. 840).

             We need to do something, because once the user implements (with a macro) the
             type- or cg-polymorphic definition, they will receive those type-names as arguments (to
             be leveraged by the macro definition), meaning they will need access to those type
             definitions to successfully implement the macro. (See Kyber for examples of this.)

             Therefore, we treat this as a cross-call from the external function prototype (even
             though it most likely won't be emitted, since it's too polymorphic for C), towards the
             type definitions themselves. Thanks to the three cases above, we can simply substitute
             and recursively visit. *)
          let lid = Helpers.assert_elid e.node in
          (* This needs to be kept in sync with include/eurydice_glue.h *)
          let external_call_needs_return_type =
            match lid with
            | ["Eurydice"], "slice_to_array2"
            | ["Eurydice"], "into_iter"
            | ["LowStar"], "ignore" -> false
            | _ -> true
          in
          List.iter ((visit lid false)#visit_typ ())
            (if external_call_needs_return_type then t :: ts else ts)

        method! visit_EQualified _ name =
          (* Cross-compilation unit calls force the callee to become visible, at
             least through an internal header. *)
          if cross_call lid name then
            raise name Internal;
          (* See above *)
          if cross_crate lid name then
            raise name Workspace;
          (* Mutually recursive calls require the prototype to be in scope, at
             least through the internal header. *)
          if not (LidSet.mem name !seen) then
            raise name Internal;
          (* Static inline definitions force the callee to be at least as
             visible as the caller, so that the callee is in scope of the
             caller. *)
          if my_info.inlining = StaticInline then
            record_call_from_to lid name;
          (* Unrelated to visibility: MSVC and CompCert follow the C standard
             closely and make inline
             functions no externally-visible (which would result in a linking
             error for us). *)
          if cross_call lid name && not (Options.rust ()) then
            maybe_strip_inline name;
          (* Unrelated to visibility: WASM can't handle cross-module references
             to mutable globals. We mark this definition as needing a getter. *)
          if cross_call lid name then
            maybe_needs_getter name
      end in

      let visit = visit lid in

      begin match d with
      | DFunction (_, _, _, _, t, _, bs, e) ->
          (visit false)#visit_typ () t;
          (visit false)#visit_binders_w () bs;
          (visit true)#visit_expr_w () e
      | DGlobal (_, _, _, t, e) ->
          (visit false)#visit_typ () t;
          (* Even though the grammar of C global variable initializers is very
             limited, this is still useful e.g. in the presence of function
             pointers. *)
          (visit true)#visit_expr_w () e
      | DExternal (_, _, _, _, _, t, _) ->
          (visit false)#visit_typ () t
      | DType (_, _flags, _, _, d) ->
          (visit false)#visit_type_def () d
      end;
      seen := LidSet.add lid !seen
    ) decls
  ) files;

  (* Fixpoint computation *)
  let module F = Fix.Fix.ForOrderedType(struct
    type t = lident
    let compare = Stdlib.compare
  end)(struct
    type property = visibility
    let bottom = Private
    let equal = (=)
    let is_maximal = (=) Public
  end) in
  let valuation = F.lfp (fun lid valuation ->
    if not (Hashtbl.mem info_map lid) then
      Warn.fatal_error "No equation for %a" plid lid;
    let info = Hashtbl.find info_map lid in
    let adjust caller =
      if (Hashtbl.find info_map caller).abstract_struct then
        Internal
      else
        valuation caller
    in
    LidSet.fold (fun caller v -> lub v (adjust caller)) info.callers info.visibility
  ) in

  (* Adjust definitions based on `info_map` updated with fixpoint *)
  let files = List.map (fun (f, decls) ->
    f, List.map (fun d ->
      let lid = lid_of_decl d in
      let info = Hashtbl.find info_map lid in
      let old_vis = info.visibility in
      (* Fixpoint computation *)
      let info = { info with visibility = valuation (lid_of_decl d) } in
      (* C abstract structs are treated as internal for the purposes of visibility computation,
         but the convention is that they end up being marked as public for CStarToC11 to do the
         right thing. (This may need fixing.) *)
      let info = { info with visibility = if info.abstract_struct then Public else info.visibility } in
      if Options.debug "visibility-fixpoint" then
        KPrint.bprintf "[adjustment]: %a: %a --> %a, wasm: mut %b getter %b\n"
          plid lid pvis old_vis pvis info.visibility info.wasm_mutable info.wasm_needs_getter;

      let remove_if cond flag flags = if cond then List.filter ((<>) flag) flags else flags in
      let add_if cond flag flags = if cond && not (List.mem flag flags) then flag :: flags else flags in
      let adjust flags =

        let flags = remove_if (info.inlining = Nope) Common.Inline flags in
        let flags = remove_if (info.inlining = Nope) Common.MustInline flags in
        let flags = remove_if (info.visibility <> Private) Common.Private flags in
        let flags = add_if (info.visibility = Private) Common.Private flags in
        let flags = remove_if (info.visibility <> Internal) Common.Internal flags in
        let flags = add_if (info.visibility = Internal) Common.Internal flags in
        let flags = remove_if (info.visibility <> Workspace) Common.Workspace flags in
        let flags = add_if (info.visibility = Workspace) Common.Workspace flags in
        if Options.wasm () then
          (* We override the previous logic in the case of WASM *)
          let flags = remove_if info.wasm_mutable Common.Internal flags in
          let flags = add_if info.wasm_mutable Common.Private flags in
          flags
        else
          flags
      in
      match d with
      | DFunction (cc, flags, n_cgs, n, t, name, bs, e) ->
          DFunction (cc, adjust flags, n_cgs, n, t, name, bs, e)
      | DGlobal (flags, name, n, t, e) ->
          DGlobal (adjust flags, name, n, t, e)
      | DExternal (cc, flags, n_cg, n, name, t, hints) ->
          DExternal (cc, adjust flags, n_cg, n, name, t, hints)
      | DType (name, flags, n_cgs, n, def) ->
          DType (name, adjust flags, n_cgs, n, def)
    ) decls
  ) files in

  (* WASM compilers error out when a module tries to directly access a mutable
     global constant for another module (this appears to work on OSX but not
     other OSes for dynamic linking issues I don't pretend to understand). We
     detect those accesses here too, and when N.f accesses M.x, we generate
     M.__get_x, and then N.f calls `M.__get_x ()` instead of reading `M.x`. *)
  let name_of_getter lid = fst lid, "__get_" ^ snd lid in
  let type_of_getter t = TArrow (TUnit, t) in
  let generate_getters = object
    inherit [_] map as super

    method! visit_EQualified (_, t) name =
      if (Hashtbl.find info_map name).wasm_needs_getter then
        EApp (with_type (type_of_getter t) (EQualified (name_of_getter name)), [ Helpers.eunit ])
      else
        EQualified name

    val mutable new_decls = []
    method! visit_DGlobal () flags name n t body =
      if (Hashtbl.find info_map name).wasm_needs_getter then begin
        let d = DFunction (None, [], 0, 0,
          t,
          name_of_getter name,
          [ Helpers.fresh_binder "_" TUnit ],
          with_type t (EQualified name)
        ) in
        new_decls <- d :: new_decls
      end;
      DGlobal (flags, name, n, t, body)

    method! visit_program () decls =
      new_decls <- [];
      let decls = super#visit_program () decls in
      decls @ List.rev new_decls
  end in
  let files = if Options.wasm () then generate_getters#visit_files () files else files in
  files

(** A whole-program transformation that inlines functions according to... *)

let always_live name =
  let n = fst (GlobalNames.target_c_name ~attempt_shortening:false name) in
  n = "main" ||
  String.length n >= 11 &&
  String.sub n 0 11 = "WasmSupport" &&
  Options.wasm ()

let inline files =

  let must_inline, must_disappear = inline_analysis files in

  (* We create an inliner based on this criterion. *)
  let inline_one = mk_inliner files must_inline in

  (* - Each function that must be inlined for soundness is dropped.
   * - The memoizing inliner is called for each function's body.
   * - Cross-translation unit calls are detected and [Private] qualifiers are
   *   dropped accordingly.
   * *)
  let files = filter_decls (function
    | DFunction (cc, flags, n_cgs, n, ret, name, binders, _) ->
        if must_disappear name && not (always_live name) then begin
          if Options.debug "reachability" then
            KPrint.bprintf "REACHABILITY: %a must disappear\n" plid name;
          None
        end else
          Some (DFunction (cc, flags, n_cgs, n, ret, name, binders, inline_one name))
    | DGlobal (flags, name, n, t, _) ->
        (* Note: should we allow globals to marked as "must disappear"? *)
        Some (DGlobal (flags, name, n, t, inline_one name))
    | d ->
        Some d
  ) files in

  files


let inline_type_abbrevs ?(just_auto_generated=false) files =
  let map = Helpers.build_map files (fun map -> function
    | DType (lid, flags, _, _, Abbrev t) when
      not just_auto_generated || just_auto_generated && List.mem AutoGenerated flags ->
        Hashtbl.add map lid (White, t)
    | _ -> ()
  ) in

  List.iter (fun (lid, t) -> Hashtbl.add map lid (White, t)) [
    (["Prims"], "int"), TInt CInt;
    (["Prims"], "nat"), TInt CInt;
    (["Prims"], "pos"), TInt CInt;
    (["C"; "String"], "t"), TQualified (["Prims"], "string");
  ];

  let inliner inline_one = object(self)
    inherit [_] map
    method! visit_TApp () lid ts =
      try DeBruijn.subst_tn (List.map (self#visit_typ ()) ts) (inline_one lid)
      with Not_found -> TApp (lid, List.map (self#visit_typ ()) ts)
    method! visit_TQualified () lid =
      try inline_one lid
      with Not_found -> TQualified lid
  end in

  let inline_one = memoize_inline map (fun recurse -> (inliner recurse)#visit_typ ()) in
  let i = inliner inline_one in

  let files = i#visit_files () files in
  if just_auto_generated then
    filter_decls (fun d ->
      match d with
      | DType (_, flags, _, _, Abbrev _) when List.mem AutoGenerated flags ->
          None
      | _ ->
          Some d
    ) files
  else
    files


(* Drop unused private functions **********************************************)

(* Private functions are marked as static. The C compiler errors out if a
 * function is marked as static AND is not used within this translation unit.
 * We just perform a per-file reachability analysis starting from non-private
 * functions. Note to my future self: errors may arise if the only use site is a
 * macro that drops its parameter... check krmllib.h! *)
let drop_unused files =
  let seen = Hashtbl.create 41 in

  let body_of_lid = Helpers.build_map files (fun map d -> Hashtbl.add map (lid_of_decl d) d) in

  let visitor = object (self)
    inherit [_] iter as super
    method! visit_EQualified (before, _) lid =
      self#discover before lid
    method! visit_TQualified before lid =
      self#discover before lid
    method! visit_TApp before lid ts =
      self#discover before lid;
      List.iter (self#visit_typ before) ts
    method private discover before lid =
      if not (Hashtbl.mem seen lid) then begin
        Hashtbl.add seen lid ();
        if Options.debug "reachability" then
          KPrint.bprintf "REACHABILITY: %a is used (via: %s) \n" plid lid
            (String.concat " <- " (List.map (fun lid -> KPrint.bsprintf "%a" plid lid) before));

        if Hashtbl.mem body_of_lid lid then
          ignore (super#visit_decl (lid :: before) (Hashtbl.find body_of_lid lid));
      end
    method! visit_decl _ d =
      let flags = flags_of_decl d in
      let lid = lid_of_decl d in
      if not (List.exists ((=) Private) flags) && not (Drop.lid lid) || always_live lid then begin
        if Options.debug "reachability" then
          KPrint.bprintf "REACHABILITY: %a is a root because it isn't private\n" plid lid;
        Hashtbl.add seen lid ();
        super#visit_decl [lid] d
      end
   end in
  visitor#visit_files [] files;
  Hashtbl.add seen (["LowStar"; "Ignore"], "ignore") ();
  filter_decls (fun d ->
    let flags = flags_of_decl d in
    let lid = lid_of_decl d in
    if (List.exists ((=) Private) flags || Drop.lid lid) && not (Hashtbl.mem seen lid) then
      None
    else
      Some d
  ) files

let mark_possibly_unused ifdefs files =
  let map = (object (self)
    inherit [_] reduce as super
    method zero = LidSet.empty
    method plus = LidSet.union
    method! visit_EQualified _ lid = LidSet.singleton lid
    method! visit_EIfThenElse env e1 e2 e3 =
      match Helpers.is_ifdef ifdefs e1 with
      | `No -> super#visit_EIfThenElse env e1 e2 e3
      | `Yes ->
          LidSet.union (self#visit_expr env e1)
            (LidSet.inter (self#visit_expr env e2) (self#visit_expr env e3))
      | `YesWithExtra (e1, e2') ->
          LidSet.union (self#visit_expr env e1)
            (LidSet.inter
              (LidSet.union (self#visit_expr env e2) (self#visit_expr env e2')) (self#visit_expr env e3))
  end)#visit_files () files in
  (object
    inherit [_] map
    method! visit_DFunction _ cc flags n_cgs n t name binders body =
      if not (LidSet.mem name map) && List.mem Private flags then
        DFunction (cc, MaybeUnused :: flags, n_cgs, n, t, name, binders, body)
      else
        DFunction (cc, flags, n_cgs, n, t, name, binders, body)
  end)#visit_files () files

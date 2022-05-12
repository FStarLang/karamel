(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 License. *)

(** Whole-program inlining based on the [MustDisappear] flag passed by F*. *)

open Ast
open PrintAst.Ops
open Common

(* Natural arity analysis must be performed before inlining (see comment in
 * [inline_one]. *)
let natural_arity = Hashtbl.create 43

let compute_natural_arity = object
  inherit [_] iter

  method! visit_DFunction () _ _ _ _ name args _ =
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
    | EQualified lid | ETApp ({ node = EQualified lid; _ }, _) ->
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
  let debug_inline = Options.debug "inline" in
  let wrap_comment lid term =
    if debug_inline then
      EComment (
        KPrint.bsprintf "start inlining %a" plid lid,
        term,
        KPrint.bsprintf "end inlining %a" plid lid)
    else
      term.node
  in

  (* Build a map suitable for the [memoize_inline] combinator. *)
  let map = Helpers.build_map files (fun map -> function
    | DGlobal (_, name, _, _, body)
    | DFunction (_, _, _, _, name, _, body) ->
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
          wrap_comment lid (Helpers.safe_substitution es (recurse lid) t)
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
    | DFunction (_, flags, _, _, name, _, body) ->
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
    (!Options.wasm && small_enough lid) ||
    List.mem Substitute flags ||
    must_disappear lid
  in
  must_inline, must_disappear

(** This phase drops private qualifiers if a function is called across
 * translation units. The visibility rules of F* notwithstanding, these can
 * happen because:
 * - StackInline created such a cross-call
 * - -bundle optimistically marked functions as private
 * - initializing of constants whose initial value is not a C value from the
 *   separate "krmlinit" translation unit.
 * As such, this phase must happen after all three steps above.
 * The Inline qualifier is also dropped if compiling for CompCert; for other
 * compilers, this is just a warning. *)
let cross_call_analysis files =

  let file_of = Bundle.mk_file_of files in

  let module T = struct type outcome = Private | Internal end in

  (* A map that *eventually* will contain the exactly the set of [lid]s that can
   * be safely marked as private. The invariant is not established yet. *)
  let private_or_internal = Hashtbl.create 41 in
  let safely_inline = Hashtbl.create 41 in
  let c_abstract_structs = Hashtbl.create 41 in

  (* Constants that will end up being mutable in Wasm because of the compilation
   * scheme of constants as little-endian encoded pre-laid out byte literals
   * relative to `data_start` *)
  let wasm_mutable = Hashtbl.create 41 in

  (* In the initial state, we optimistically mark every private function as
     being private, every inline function as being inline. We also anticipate
     on the WASM compilation phase and record all the globals that will be
     compiled as WASM mutable globals. *)
  List.iter (fun (_, decls) ->
    List.iter (fun d ->
      let name = lid_of_decl d in
      let flags = flags_of_decl d in

      if List.mem Private flags && not (Helpers.is_static_header name) then
        (* -static-header takes precedence over private, see CStarToC11.ml *)
        Hashtbl.add private_or_internal name T.Private;

      if List.mem AbstractStruct flags then
        Hashtbl.add c_abstract_structs name ();

      if List.mem Inline flags then
        Hashtbl.add safely_inline name ();

      match d with
      | DGlobal (_, _, _, (TBuf _ | TArray _), _) ->
          Hashtbl.add wasm_mutable name ()
      | _ ->
          ()
    ) decls
  ) files;

  let cross_call name1 name2 =
    let file1 = file_of name1 in
    let file2 = file_of name2 in
    let should_drop = function
      | Some f -> Drop.file f
      | None -> false
    in
    file1 <> file2 &&
    not (should_drop file1 || should_drop file2)
  in

  let warn_and_remove name_from name_to =
    (* There is a cross-compilation-unit call from [name_from] to
     * [name_from‘], meaning that the latter cannot safely remain
     * inline. *)
    if cross_call name_from name_to && Hashtbl.mem private_or_internal name_to then begin
      (* KPrint.bprintf "Cross-call from %a to %a which becomes internal\n" *)
      (*   plid name_from plid name_to; *)
      Hashtbl.replace private_or_internal name_to T.Internal
    end;
    if cross_call name_from name_to && Hashtbl.mem safely_inline name_to &&
      not (Helpers.is_static_header name_to)
    then begin
      Warn.maybe_fatal_error ("", LostInline (file_of name_from, name_from, file_of name_to, name_to));
      Hashtbl.remove safely_inline name_to
    end
  in

  let getters = Hashtbl.create 41 in
  let name_of_getter lid =
    fst lid, "__get_" ^ snd lid
  in
  let type_of_getter t = TArrow (TUnit, t) in

  (* A visitor that, when passed a function's name and body, detects
   * cross-translation unit calls and modifies safely_private and safely_inline
   * accordingly. *)
  let unmark_private_in = object
    inherit [_] map as super
    val mutable name = [],""
    method! visit_EQualified ((_, t) as env) name' =
      if !Options.wasm && cross_call name name' && Hashtbl.mem wasm_mutable name' then begin
        if Options.debug "wasm" then
          KPrint.bprintf "%a accesses %a, a mutable global, across modules: getter \
            must be generated\n" plid name plid name';
        Hashtbl.add getters name' ();
        EApp (with_type (type_of_getter t) (EQualified (name_of_getter name')),
          [ Helpers.eunit ])
      end else begin
        warn_and_remove name name';
        super#visit_EQualified env name'
      end

    method! visit_TQualified () name' =
      warn_and_remove name name';
      super#visit_TQualified () name'

    method! visit_TApp () name' ts =
      warn_and_remove name name';
      super#visit_TApp () name' ts

    method! visit_decl () d =
      name <- lid_of_decl d;
      super#visit_decl () d
  end in
  let files = unmark_private_in#visit_files () files in

  (* WASM compilers error out when a module tries to directly access a mutable
     global constant for another module (this appears to work on OSX but not
     other OSes for dynamic linking issues I don't pretend to understand). We
     detect those accesses here too, and when N.f accesses M.x, we generate
     M.__get_x, and then N.f calls `M.__get_x ()` instead of reading `M.x`. *)
  let generate_getters = object
    inherit [_] map as super
    val mutable new_decls = []
    method! visit_DGlobal () flags name n t body =
      if Hashtbl.mem getters name then begin
        let d = DFunction (None, [], 0,
          t,
          name_of_getter name,
          [ Helpers.fresh_binder "_" TUnit ],
          with_type t (EQualified name)
        ) in
        new_decls <- d :: new_decls
      end;

      let flags =
        if Hashtbl.mem wasm_mutable name then begin
          Hashtbl.add private_or_internal name Private;
          Common.Private :: flags
        end else
          flags
      in

      DGlobal (flags, name, n, t, body)

    method! visit_program () decls =
      new_decls <- [];
      let decls = super#visit_program () decls in
      decls @ List.rev new_decls
  end in
  let files = if !Options.wasm then generate_getters#visit_files () files else files in

  (* Another visitor, that only visits the types reachable from types in
   * function definitions and removes their private qualifiers accordingly. For
   * static inline functions (whose bodies end up in the header file), we need
   * to visit the bodies as well. *)
  let unmark_private_types_in =
    let decl_map = Helpers.build_map files (fun map d ->
      match d with
      | DType (lid, _, _, _) -> Hashtbl.add map lid d
      | _ -> ()
    ) in
    let seen = Hashtbl.create 41 in
    (* TODO: switch to a fixpoint calculation... this is bad *)
    let mode = ref `Internal in
    let mode_lt x y =
      match x, y with
      | `Internal, `Public -> true
      | _ -> false
    in
    object (self)
      inherit [_] iter as super

      method private still_private d =
        List.mem Private (flags_of_decl d) &&
        Hashtbl.find_opt private_or_internal (lid_of_decl d) = Some T.Private

      method private remove_and_visit name =
        (* KPrint.bprintf "Remove_and_visit %a with mode %s\n" plid name *)
        (*   (match !mode with `Public -> "public" | `Internal -> "internal"); *)
        if Hashtbl.mem private_or_internal name then begin
          match !mode with
          | `Internal ->
              Hashtbl.replace private_or_internal name T.Internal
          | `Public ->
              Hashtbl.remove private_or_internal name
        end;
        if (not (Hashtbl.mem seen name) || mode_lt (Hashtbl.find seen name) !mode) then begin
          Hashtbl.replace seen name !mode;
          if not (Hashtbl.mem c_abstract_structs name) then
            try super#visit_decl () (Hashtbl.find decl_map name)
            with Not_found -> ()
        end

      method! visit_TQualified () name =
        self#remove_and_visit name

      method! visit_TApp () name ts =
        self#remove_and_visit name;
        List.iter (self#visit_typ ()) ts

      method! visit_DFunction () _ _ _ ret name binders body =
        self#visit_typ () ret;
        self#visit_binders_w () binders;
        if Helpers.is_static_header name then
          self#visit_expr_w () body

      method! visit_DGlobal () _ name _ typ body =
        self#visit_typ () typ;
        if Helpers.is_static_header name then
          self#visit_expr_w () body

      (* Traversal starts here at the top-level. Note that remove_and_visit does
         not call into this method (but rather the default one via super). *)
      method! visit_decl env d =
        (* KPrint.bprintf "Visiting %a?? still_private=%b\n" plid (lid_of_decl d) (self#still_private d); *)
        (* We visit any non-private declaration; static header takes precedence
           over private. *)
        let name = lid_of_decl d in
        let flags = flags_of_decl d in
        if (not (self#still_private d) || Helpers.is_static_header name) &&
          not (List.mem AbstractStruct flags)
        then begin
          mode :=
            match Hashtbl.find private_or_internal name with
            | exception Not_found -> `Public
            | T.Internal -> `Internal
            | T.Private -> assert (Helpers.is_static_header name); `Public ; ;
          Hashtbl.add seen (lid_of_decl d) !mode;
          (* KPrint.bprintf "Visiting %a with mode %s\n" plid (lid_of_decl d) *)
          (*   (match !mode with `Public -> "public" | `Internal -> "internal"); *)
          super#visit_decl env d
        end
    end
  in
  unmark_private_types_in#visit_files () files;

  (* The invariant for [safely_private] is now established, and we drop those
   * functions that cannot keep their [Private] flag. *)
  let files =
    let keep_if table flag name flags =
      if not (Hashtbl.mem table name) ||
        (* TODO why? `main` can neither be inline or private ?! *)
        GlobalNames.target_c_name ~attempt_shortening:false ~is_macro:false name = "main"
      then
        List.filter ((<>) flag) flags
      else
        flags
    in
    let filter name flags =
      let flags =
        match Hashtbl.find private_or_internal name with
        | exception Not_found -> List.filter ((<>) Private) flags
        | T.Private -> flags
        | T.Internal -> Internal :: List.filter ((<>) Private) flags
      in
      (* KPrint.bprintf "%a: %s\n" plid name (String.concat " " (List.map show_flag flags)); *)
      if !Options.cc = "compcert" then
        keep_if safely_inline Inline name flags
      else
        flags
    in
    map_decls (function
      | DFunction (cc, flags, n, ret, name, binders, body) ->
          DFunction (cc, filter name flags, n, ret, name, binders, body)
      | DGlobal (flags, name, n, e, t) ->
          DGlobal (filter name flags, name, n, e, t)
      | DExternal (cc, flags, name, t, pp) ->
          DExternal (cc, filter name flags, name, t, pp)
      | DType (name, flags, n, t) ->
          DType (name, filter name flags, n, t)
    ) files
  in

  files

(** A whole-program transformation that inlines functions according to... *)

let always_live name =
  let n = GlobalNames.target_c_name ~attempt_shortening:false ~is_macro:false name in
  n = "main" ||
  String.length n >= 11 &&
  String.sub n 0 11 = "WasmSupport" &&
  !Options.wasm

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
    | DFunction (cc, flags, n, ret, name, binders, _) ->
        if must_disappear name && not (always_live name) then begin
          if Options.debug "reachability" then
            KPrint.bprintf "REACHABILITY: %a must disappear\n" plid name;
          None
        end else
          Some (DFunction (cc, flags, n, ret, name, binders, inline_one name))
    | DGlobal (flags, name, n, t, _) ->
        (* Note: should we allow globals to marked as "must disappear"? *)
        Some (DGlobal (flags, name, n, t, inline_one name))
    | d ->
        Some d
  ) files in

  files


let inline_type_abbrevs files =
  let map = Helpers.build_map files (fun map -> function
    | DType (lid, _, _, Abbrev t) -> Hashtbl.add map lid (White, t)
    | _ -> ()
  ) in

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

  (* There may be type abbreviations in here... since we recorded the naming
     hints early! So, expand them there, too. *)
  NamingHints.hints := List.map (fun ((hd, args), lid) ->
    (hd, List.map (i#visit_typ ()) args), lid
  ) !NamingHints.hints;

  (* After we've inlined things, drop type abbreviations definitions now. This
   * is important, as the monomorphization of data types relies on all types
   * being fully applied (i.e. no more TBound), and leaving things such as:
   *   type pair a b = Tuple (1, 0)
   * breaks this invariant. *)
  filter_decls (function
    | DType (lid, _, n, Abbrev def) as d ->
        let hint_preferred_name = match def with
          | TApp (hd, args) ->
              List.assoc_opt (hd, args) !NamingHints.hints
          | TTuple args ->
              List.assoc_opt (tuple_lid, args) !NamingHints.hints
          | _ ->
              None
        in
        if hint_preferred_name = Some lid then
          (* We are about to generate a monomorphized instance with this very
             name. We don't want two type definitions with the same name. Drop
             it. *)
          None
        else if n > 0 then
          None
        else
          Some d

    | d ->
        Some d
  ) files


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
  filter_decls (fun d ->
    let flags = flags_of_decl d in
    let lid = lid_of_decl d in
    if (List.exists ((=) Private) flags || Drop.lid lid) && not (Hashtbl.mem seen lid) then
      None
    else
      Some d
  ) files

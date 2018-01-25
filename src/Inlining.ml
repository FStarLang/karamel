(** Make sure the notion of Low* frames is soundly implemented in C*. In
 * particular, if a function doesn't push/pop a frame _and_ allocates, then it
 * originates from the [StackInline] or [Inline] effects and must be inlined so
 * as to perform allocations in its parent frame. *)

(** We perform a fixpoint computation on the following simple lattice:

    mustinline
      |
    safe

 * This is a whole-program analysis.
*)

open Ast
open Warnings
open PrintAst.Ops
open Common

(* Two distinguished cases that are always live and shall not be eliminated from
 * the program, no matter what: the main function, and UInt128 (which kremlib.h
 * assumes is always in scope). *)
let always_live name =
  (* kremlib.h assumes this type exists, so keep it, even if the program
   * doesn't use uint128. *)
  let always_live = [
    [ "FStar"; "UInt128" ], "uint128"
  ] in
  let always_live_c = [
    "main"
  ] in
  List.mem name always_live ||
  List.mem (Simplify.target_c_name name) always_live_c


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
      fatal_error "[Frames]: cyclic dependency on %a" plid lid
  | Black ->
      body
  | White ->
      Hashtbl.add map lid (Gray, body);
      let body = visit (memoize_inline map visit) body in
      Hashtbl.add map lid (Black, body);
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
          wrap_comment lid (Helpers.safe_substitution es (recurse lid) t)
      | _ ->
          EApp (self#visit_expr_w () e, es)
    method! visit_EQualified (_, t) lid =
      match t with
      | TArrow _ when Hashtbl.mem map lid && criterion lid ->
          fatal_error "[Frames]: partially applied function; not meant to happen";
      | _ ->
          EQualified lid
  end)#visit_expr_w ()) in
  inline_one

(** Relying on the MustDisappear flag passed by F* ****************************)

let inline_analysis files =
  (* ... our criterion for determining whether a function must be inlined or not...
   * ... we map each [lid] to a pair of:
   * - a boolean, i.e. whether the user demanded inlining (via the
   *   substitute attribute), and
   * - the body, which [inline_analysis] needs to figure out if the function
   *   allocates without pushing a frame, meaning it must be inlined. *)
  let map = Helpers.build_map files (fun map -> function
    | DFunction (_, flags, _, _, name, _, _) ->
        Hashtbl.add map name flags
    | _ ->
        ()
  ) in
  Hashtbl.add map ([ "kremlinit" ], "globals") [];
  let must_disappear lid =
    List.mem MustDisappear (Hashtbl.find map lid)
  in
  let must_inline lid =
    List.mem Substitute (Hashtbl.find map lid) ||
    must_disappear lid
  in
  must_inline, must_disappear


(** This phase drops private qualifiers if a function is called across
 * translation units. The visibility rules of F* notwithstanding, these can
 * happen because:
 * - StackInline created such a cross-call
 * - -bundle optimistically marked functions as private
 * - initializing of constants whose initial value is not a C value from the
 *   separate "kremlinit" translation unit.
 * As such, this phase must happen after all three steps above.
 * The Inline qualifier is also dropped if compiling for CompCert; for other
 * compilers, this is just a warning. *)
let cross_call_analysis files =

  (* A map that *eventually* will contain the exactly the set of [lid]s that can
   * be safely marked as private. The invariant is not established yet. *)
  let safely_private = Hashtbl.create 41 in
  let safely_inline = Hashtbl.create 41 in
  List.iter (fun (_, decls) ->
    List.iter (fun d ->
      let name = lid_of_decl d in
      let flags = flags_of_decl d in
      if List.mem Private flags then
        Hashtbl.add safely_private name ();
      if List.mem CInline flags then
        Hashtbl.add safely_inline name ()
    ) decls
  ) files;

  (* Note that because of bundling, we no longer have the invariant that the
   * left-hand-side of an [lident] maps to the name of the file it originates
   * from. *)
  let file_of = Bundle.mk_file_of files in

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
    if cross_call name_from name_to && Hashtbl.mem safely_private name_to then begin
      Warnings.maybe_fatal_error ("", LostStatic (file_of name_from, name_from, file_of name_to, name_to));
      Hashtbl.remove safely_private name_to
    end;
    if cross_call name_from name_to && Hashtbl.mem safely_inline name_to then begin
      Warnings.maybe_fatal_error ("", LostInline (file_of name_from, name_from, file_of name_to, name_to));
      Hashtbl.remove safely_inline name_to
    end
  in

  (* A visitor that, when passed a function's name and body, detects
   * cross-translation unit calls and modifies safely_private and safely_inline
   * accordingly. *)
  let unmark_private_in = object (self)
    inherit [_] iter as super
    val mutable name = [],""
    method! visit_EQualified _ name' =
      warn_and_remove name name'
    method! visit_TQualified () name' =
      warn_and_remove name name'
    method! visit_TApp () name' ts =
      warn_and_remove name name';
      List.iter (self#visit_typ ()) ts
    method! visit_decl () d =
      name <- lid_of_decl d;
      super#visit_decl () d
  end in
  unmark_private_in#visit_files () files;

  (* Another visitor, that only visits the types reachable from types in
   * function definitions and removes their private qualifiers accordingly. *)
  let unmark_private_types_in =
    let decl_map = Helpers.build_map files (fun map d ->
      match d with
      | DType (lid, _, _, d) -> Hashtbl.add map lid d
      | _ -> ()
    ) in
    let seen = Hashtbl.create 41 in
    object (self)
      inherit [_] iter as super

      method private remove_and_visit name =
        if Hashtbl.mem safely_private name then
          Hashtbl.remove safely_private name;
        if not (Hashtbl.mem seen name) then begin
          Hashtbl.add seen name ();
          try self#visit_type_def () (Hashtbl.find decl_map name)
          with Not_found -> ()
        end

      method! visit_TQualified () name =
        self#remove_and_visit name

      method! visit_TApp () name ts =
        self#remove_and_visit name;
        List.iter (self#visit_typ ()) ts

      method! visit_DFunction () _ _ _ ret _ binders _ =
        self#visit_typ () ret;
        self#visit_binders_w () binders

      method! visit_DGlobal () _ _ _ typ _ =
        self#visit_typ () typ

      method! visit_expr _ _ =
        assert false

      method! visit_decl env d =
        if not (List.mem Private (flags_of_decl d)) then begin
          Hashtbl.add seen (lid_of_decl d) ();
          super#visit_decl env d
        end
    end
  in
  let uint128_lid = [ "FStar"; "UInt128" ], "uint128" in
  if Hashtbl.mem safely_private uint128_lid then
    Hashtbl.remove safely_private uint128_lid;
  unmark_private_types_in#visit_files () files;

  (* The invariant for [safely_private] is now established, and we drop those
   * functions that cannot keep their [Private] flag. *)
  let files =
    let keep_if table flag name flags =
      if not (Hashtbl.mem table name) || Simplify.target_c_name name = "main" then
        List.filter ((<>) flag) flags
      else
        flags
    in
    let filter name flags =
      let flags = keep_if safely_private Private name flags in
      if !Options.cc = "compcert" then
        keep_if safely_inline CInline name flags
      else
        flags
    in
    map_decls (function
      | DFunction (cc, flags, n, ret, name, binders, body) ->
          DFunction (cc, filter name flags, n, ret, name, binders, body)
      | DGlobal (flags, name, n, e, t) ->
          DGlobal (filter name flags, name, n, e, t)
      | DExternal (cc, flags, name, t) ->
          DExternal (cc, filter name flags, name, t)
      | DType (name, flags, n, t) ->
          DType (name, filter name flags, n, t)
    ) files
  in

  files

(** A whole-program transformation that inlines functions according to... *)
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
            KPrint.bprintf "REACHABILITY: %a must disappear, because it's StackInline\n" plid name;
          None
        end else
          Some (DFunction (cc, flags, n, ret, name, binders, inline_one name))
    | d ->
        (* Note: not inlining globals because F* should forbid top-level
         * effects...? *)
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

  let files = (inliner inline_one)#visit_files () files in

  (* After we've inlined things, drop type abbreviations definitions now. This
   * is important, as the monomorphization of data types relies on all types
   * being fully applied (i.e. no more TBound), and leaving things such as:
   *   type pair a b = Tuple (1, 0)
   * breaks this invariant. *)
  filter_decls (function
    | DType (lid, flags, n, Abbrev def) ->
        if n = 0 then
          Some (DType (lid, flags, n, Abbrev def))
        else
          (* A type definition with parameters is not something we'll be able to
           * generate code for (at the moment). So, drop it. *)
          None
    | d ->
        Some d
  ) files


(* Drop unused private functions **********************************************)

(* Private functions are marked as static. The C compiler errors out if a
 * function is marked as static AND is not used within this translation unit.
 * We just perform a per-file reachability analysis starting from non-private
 * functions. Note to my future self: errors may arise if the only use site is a
 * macro that drops its parameter... check kremlib.h! *)
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

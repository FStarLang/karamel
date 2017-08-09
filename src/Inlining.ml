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

(** A fixpoint computation ****************************************************)

(** Data structures required by [Fix] *)

module LidMap = Idents.LidMap

module ILidMap = struct
  type key = lident
  type 'data t = 'data LidMap.t ref
  let create () = ref LidMap.empty
  let clear m = m := LidMap.empty
  let add k v m = m := LidMap.add k v !m
  let find k m = LidMap.find k !m
  let iter f m = LidMap.iter f !m
end

type property = Safe | MustInline

let lub x y =
  match x, y with
  | Safe, Safe -> Safe
  | _ -> MustInline

module Property = struct
  type nonrec property = property
  let bottom = Safe
  let equal = (=)
  let is_maximal p = p = MustInline
end

module F = Fix.Make(ILidMap)(Property)

(** The actual fixpoint computation; if [f] does not push a frame and calls [g],
 * and [g] must be inlined, then [f] must be inlined too. *)
let inline_analysis map =
  let lookup lid = Hashtbl.find map lid in
  let debug_inline = Options.debug "inline" in

  (** To determine whether a function should be inlined, we use a syntactic
   * criterion: any buffer allocation that happens before a [push_frame] implies
   * the function must be inlined to be sound. Any reference to an external
   * function also is enough of a reason to inline. *)
  (** TODO: this criterion is not sound as it stands because we should also
   * check what happens _after_ the EPopFrame. *)
  let contains_alloc lid valuation expr =
    let module L = struct exception Found of string end in
    try
      ignore ((object
        inherit [_] map as super
        method! ebufcreate () t l e =
          if l = Stack then
            raise (L.Found "bufcreate")
          else
            super#ebufcreate () t l e
        method! ebufcreatel () t l e =
          if l = Stack then
            raise (L.Found "bufcreateL")
          else
            super#ebufcreatel () t l e
        method! equalified () t lid =
          (* In case we ever decide to allow wacky stuff like:
           *   let f = if ... then g else h in
           *   ignore f;
           * then this will become an over-approximation. *)
          match t with
          | TArrow _ when valuation lid = MustInline ->
              raise (L.Found (KPrint.bsprintf "transitive: %a" plid lid))
          | _ ->
              super#equalified () t lid
      end)#visit () expr);
      false
    with L.Found reason ->
      if debug_inline then
        KPrint.bprintf "%a will be inlined because: %s\n" plid lid reason;
      true
  in

  let must_inline lid valuation =
    let contains_alloc = contains_alloc lid in
    let rec walk e =
      match e.node with
      | ELet (_, body, cont) ->
          contains_alloc valuation body || walk cont
      | ESequence es ->
          let rec walk = function
            | { node = EPushFrame; _ } :: _ ->
                false
            | e :: es ->
                contains_alloc valuation e || walk es
            | [] ->
                false
          in
          walk es
      | EPushFrame ->
          fatal_error "Malformed function body %a" plid lid
      | EIfThenElse (e1, e2, e3) ->
          contains_alloc valuation e1 ||
          walk e2 ||
          walk e3
      | ESwitch (e, branches) ->
          contains_alloc valuation e ||
          List.exists (fun (_, e) ->
            walk e
          ) branches
      | EMatch (e, branches) ->
          contains_alloc valuation e ||
          List.exists (fun (_, _, e) ->
            walk e
          ) branches
      | _ ->
          contains_alloc valuation e
    in
    match lookup lid with
    | exception Not_found ->
        (* Reference to an undefined, external function. This is sound only if
         * externally-realized functions execute in their own stack frame, which
         * is fine, because they actually are, well, functions written in C. *)
        Safe
    | _, body ->
        (* Whether the function asked to be substituted is not relevant for
         * this fixpoint computation. *)
        if walk body then begin
          MustInline
        end else
          Safe
  in

  F.lfp must_inline


(* Inlining of function bodies ************************************************)

(** For each declaration in [files], call [f map decl], where [map] is the map
 * being filled. *)
let build_map files f =
  let map = Hashtbl.create 41 in
  iter_decls (f map) files;
  map

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
let mk_inliner files must_inline =
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
  let map = build_map files (fun map -> function
    | DFunction (_, _, _, _, name, _, body) ->
        Hashtbl.add map name (White, body)
    | _ ->
        ()
  ) in
  let inline_one = memoize_inline map (fun recurse -> (object(self)
    inherit [unit] map
    method eapp () t e es =
      let es = List.map (self#visit ()) es in
      match e.node with
      | EQualified lid when Hashtbl.mem map lid && must_inline lid ->
          wrap_comment lid (Helpers.safe_substitution es (recurse lid) t)
      | _ ->
          EApp (self#visit () e, es)
    method equalified () t lid =
      match t with
      | TArrow _ when Hashtbl.mem map lid && must_inline lid ->
          fatal_error "[Frames]: partially applied function; not meant to happen";
      | _ ->
          EQualified lid
  end)#visit ()) in
  inline_one


let inline_combinators files =
  (* Polymorphic functions that are marked as substitute are expanded; this MUST
   * GO AWAY and be properly performed at the KreMLin level. *)
  let map = build_map files (fun map -> function
    | DFunction (_, flags, n, _, name, _, _) ->
        if n > 0 && not (List.mem Substitute flags) && not (Drop.lid name) then
          Warnings.(maybe_fatal_error ("<toplevel>", NoPolymorphism name));
        Hashtbl.add map name (n > 0 && List.mem Substitute flags)
    | _ ->
        ()
  ) in
  let must_inline = function
    | [ "C"; "Loops" ], ("map" | "map2" | "in_place_map" | "in_place_map2" | "repeat") ->
        true
    | lid ->
        try
          Hashtbl.find map lid
        with Not_found ->
          false
  in
  let inline_one = mk_inliner files must_inline in
  filter_decls (function
    | DFunction (cc, flags, n, ret, name, binders, _) ->
        if must_inline name then
          None
        else
          let body = inline_one name in
          let body = (object
            inherit [_] map
            method tbound _ _ =
              TAny
          end)#visit () body in
          Some (DFunction (cc, flags, n, ret, name, binders, body))
    | d ->
        Some d
  ) files


(** A whole-program transformation that inlines functions according to... *)
let inline_function_frames files =

  (* ... our criterion for determining whether a function must be inlined or not... *)
  let must_inline, must_disappear =
    (* ... we map each [lid] to a pair of:
     * - a boolean, i.e. whether the user demanded inlining (via the
     *   substitute attribute), and
     * - the body, which [inline_analysis] needs to figure out if the function
     *   allocates without pushing a frame, meaning it must be inlined. *)
    let map = build_map files (fun map -> function
      | DFunction (_, flags, _, _, name, _, body) ->
          Hashtbl.add map name (List.exists ((=) Substitute) flags, body)
      | _ ->
          ()
    ) in
    let valuation = inline_analysis map in
    let must_disappear lid = valuation lid = MustInline in
    let must_inline lid = fst (Hashtbl.find map lid) || must_disappear lid in
    must_inline, must_disappear
  in

  (* We create an inliner based on this criterion. *)
  let inline_one = mk_inliner files must_inline in

  (* A map that *eventually* will contain the exactly the set of [lid]s that can
   * be safely marked as private. The invariant is not established yet. *)
  let safely_private = Hashtbl.create 41 in
  let safely_inline = Hashtbl.create 41 in
  List.iter (fun (_, decls) ->
    List.iter (function
      | DGlobal (flags, name, _, _)
      | DFunction (_, flags, _, _, name, _, _) ->
          if List.mem Private flags then
            Hashtbl.add safely_private name ();
          if List.mem CInline flags then
            Hashtbl.add safely_inline name ()
      | _ ->
          ()
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

  (* A visitor that, when passed a function's name and body, detect
   * cross-translation unit calls and drops the [Private] qualifier from the
   * callee. *)
  let unmark_private_in name body =
    let warn_and_remove name' =
      (* There is a cross-compilation-unit call from [name] to
       * [name‘], meaning that the latter cannot safely remain
       * inline. *)
      if cross_call name name' && Hashtbl.mem safely_private name' then begin
        Warnings.maybe_fatal_error ("", LostStatic (file_of name, name, file_of name', name'));
        Hashtbl.remove safely_private name'
      end;
      if cross_call name name' && Hashtbl.mem safely_inline name' then begin
        Warnings.maybe_fatal_error ("", LostInline (file_of name, name, file_of name', name'));
        Hashtbl.remove safely_inline name'
      end
    in
    ignore ((object(self)
      inherit [unit] map
      method eapp () _ e es =
        match e.node with
        | EQualified name' ->
            warn_and_remove name';
            EApp (e, List.map (self#visit ()) es)
        | _ ->
            EApp (self#visit () e, List.map (self#visit ()) es)
      method equalified () _ name' =
        warn_and_remove name';
        EQualified name'
    end)#visit () body)
  in

  (* - Each function that must be inlined for soundness is dropped.
   * - The memoizing inliner is called for each function's body.
   * - Cross-translation unit calls are detected and [Private] qualifiers are
   *   dropped accordingly.
   * *)
  let files = filter_decls (function
    | DFunction (cc, flags, n, ret, name, binders, _) ->
        if must_disappear name && Simplify.target_c_name name <> "main" then
          None
        else
          let body = inline_one name in
          unmark_private_in name body;
          Some (DFunction (cc, flags, n, ret, name, binders, body))
    | d ->
        (* Note: not inlining globals because F* should forbid top-level
         * effects...? *)
        Some d
  ) files in

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
    filter_decls (function
      | DFunction (cc, flags, n, ret, name, binders, body) ->
          Some (DFunction (cc, filter name flags, n, ret, name, binders, body))
      | DGlobal (flags, name, e, t) ->
          Some (DGlobal (filter name flags, name, e, t))
      | d ->
          Some d
    ) files
  in

  files


(* Monomorphize types *********************************************************)

let inline_type_abbrevs files =
  let map = build_map files (fun map -> function
    | DType (lid, _, _, Abbrev t) -> Hashtbl.add map lid (White, t)
    | _ -> ()
  ) in

  let inliner inline_one = object(self)
    inherit [unit] map
    method tapp () lid ts =
      try DeBruijn.subst_tn (inline_one lid) (List.map (self#visit_t ()) ts)
      with Not_found -> TApp (lid, List.map (self#visit_t ()) ts)
    method tqualified () lid =
      try inline_one lid
      with Not_found -> TQualified lid
  end in

  let inline_one = memoize_inline map (fun recurse -> (inliner recurse)#visit_t ()) in

  let files = Helpers.visit_files () (inliner inline_one) files in

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


(* Type applications are needed by the checker, even though they may refer to
 * things we won't compile, ever (e.g. from Prims). *)
let drop_type_applications files =
  Helpers.visit_files () (object
    inherit [unit] map
    method tapp _ _ _ =
      TAny
  end) files


(* Drop unused private functions **********************************************)

(* Private functions are marked as static. The C compiler errors out if a
 * function is marked as static AND is not used within this translation unit.
 * We just perform a per-file reachability analysis starting from non-private
 * functions. Note to my future self: errors may arise if the only use site is a
 * macro that drops its parameter... check kremlib.h! *)
let drop_unused files =
  (** Serves the dual purpose of marking which nodes have been visited (for the
   * graph traversal) and, as a consequence, of knowning for a given private
   * function if it was reachable starting from a non-private one. *)
  let visited = Hashtbl.create 41 in
  let body_of_lid = build_map files (fun map -> function
    | DFunction (_, _, _, _, name, _, body)
    | DGlobal (_, name, _, body) ->
        Hashtbl.add map name body
    | _ ->
        ()
  ) in
  let rec visit before lid =
    if Hashtbl.mem visited lid then
      ()
    else begin
      Hashtbl.add visited lid ();
      if Options.debug "reachability" then
        KPrint.bprintf "marking %a as used (via: %s) \n" plid lid
          (String.concat " <- " (List.map (fun lid -> KPrint.bsprintf "%a" plid lid) before));
      match Hashtbl.find body_of_lid lid with
      | exception Not_found -> ()
      | body -> visit_e (lid :: before) body
    end
  and visit_e before body =
    ignore ((object
      inherit [_] map
      method equalified () _ lid =
        visit before lid;
        EQualified lid
    end)#visit () body)
  in
  iter_decls (function
    | DFunction (_, flags, _, _, lid, _, body)
    | DGlobal (flags, lid, _, body) ->
        if not (List.exists ((=) Private) flags) && not (Drop.lid lid) then begin
          Hashtbl.add visited lid ();
          visit_e [lid] body
        end
    | _ ->
        ()
  ) files;
  filter_decls (fun d ->
    match d with
    | DGlobal (flags, lid, _, _)
    | DFunction (_, flags, _, _, lid, _, _) ->
        if (List.exists ((=) Private) flags || Drop.lid lid) && not (Hashtbl.mem visited lid) then
          None
        else
          Some d
    | d ->
        Some d
  ) files

let drop_polymorphic_functions files =
  filter_decls (function
    | Ast.DFunction (_, _, n, _, _, _, _) when n > 0 ->
        None
    | _ as d ->
        Some d
  ) files

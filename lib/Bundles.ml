(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 and MIT Licenses. *)

(** Collapsing several F* modules into a single "bundle" to allow more static
 * uses. *)

open Bundle
open Ast

module StringMap = Map.Make(String)


let uniq =
  let r = ref (-1) in
  fun () ->
    incr r;
    !r

let mark_private =
  let add_if name flags =
    let is_private = List.mem Common.Private flags in
    if not is_private && not (Inlining.always_live name) then
      Common.Private :: flags
    else
      flags
  in
  function
  | DFunction (cc, flags, n_cgs, n, typ, name, binders, body) ->
      DFunction (cc, add_if name flags, n_cgs, n, typ, name, binders, body)
  | DGlobal (flags, name, n, typ, body) ->
      DGlobal (add_if name flags, name, n, typ, body)
  | DType (lid, flags, n_cgs, n, def) ->
      DType (lid, add_if lid flags, n_cgs, n, def)
  | DExternal (cc, flags, n_cg, n, lid, t, pp) ->
      DExternal (cc, add_if lid flags, n_cg, n, lid, t, pp)

(** This collects all the files that match a given bundle specification, while
 * preserving their original dependency ordering within the bundle. If the
 * bundle is of the form Apis=Patterns, then the declarations from any of Apis
 * are kept as-is, while declarations from the modules that match the Patterns
 * are marked as private. Assuming no cross-translation-unit calls happen, this
 * means a C static qualifier in the extracted code.
 *
 * The used parameter is just here to keep track of which files have been
 * involved in at least one bundle, so that we can drop them afterwards. *)
let make_one_bundle (bundle: Bundle.t) (files: file list) (used: (int * Bundle.t) StringMap.t) =
  let debug = Options.debug "bundle" in
  if debug then
    KPrint.bprintf "Starting creation of bundle %s\n" (string_of_bundle bundle);

  let api, patterns, _ = bundle in
  (* The used map also allows us to detect when a file is used twice in a
   * bundle. *)
  let this_round = uniq () in

  let in_api_list name =
    List.mem name (List.map (String.concat "_") api)
  in

  (* Match a file against the given list of patterns. *)
  let match_file is_api patterns (used, found) (file: file) =
    List.fold_left (fun (used, found) pattern ->
      let name = fst file in
      (* [is_api] overrides the default behavior (don't collect) *)
      if Bundle.pattern_matches_file pattern name && (is_api || not (in_api_list name)) then begin
        if debug then
          KPrint.bprintf "%s is a match\n" name;

        (* If the file was already matched previously, don't match it a second time. *)
        let prev_round = try StringMap.find name used with Not_found -> max_int, ([], [], []) in
        if fst prev_round <= this_round then begin
          if is_api then
            (* Change into a non-fatal warning? Say nothing? *)
            Warn.fatal_error "The API file %s, in bundle %s, was matched \
              previously by bundle %s\n"
              name (string_of_bundle bundle) (string_of_bundle (snd prev_round));
          used, found
        end else
          let file = fst file, if is_api then snd file else List.map mark_private (snd file) in
          StringMap.add name (this_round, bundle) used, file :: found
      end else begin
        used, found
      end
    ) (used, found) patterns
  in

  (* Find all the files that match the given patterns. *)
  let used, found = List.fold_left (match_file false patterns) (used, []) files in

  (* The Api module gets a special treatment; if it exists, it is not collected
   * in the call to [fold_left] above; rather, it is taken now from the list of
   * files so that its declarations do not get the special "private" treatment. *)
  let used, found =
    if api = [] then
      used, found
    else
      let count = StringMap.cardinal used in
      if debug then
        KPrint.bprintf "Looking for bundle APIs\n";
      let used, found = List.fold_left (fun (used, found) api ->
        List.fold_left (match_file true [ Module api ]) (used, found) files
      ) (used, found) api in
      if StringMap.cardinal used <> count + List.length api then
        Warn.fatal_error "There an issue with your bundle.\n\
          You specified: -bundle %s\n\
          Here's the issue: one of these modules doesn't exist: %s.\n\
          Suggestion #1: if the file does exist, pass it to KaRaMeL.\n\
          Suggestion #2: if it doesn't, skip the %s= part and write -bundle %s"
          (string_of_bundle bundle)
          (string_of_apis api)
          (string_of_apis api)
          (string_of_patterns patterns);
      used, found
  in

  (* We return the updated map of all "used" original files *)
  let bundle = bundle_filename bundle, List.flatten (List.rev_map snd found) in
  used, bundle

type color = White | Gray | Black

type dependency = lident * string * lident * string

let string_of_dependency (d1, f1, d2, f2) =
  KPrint.bsprintf "%a (found in file %s) mentions %a (found in file %s)"
    PrintAst.plid d1 f1 PrintAst.plid d2 f2

let direct_dependencies file_of file =
  let deps = Hashtbl.create 41 in
  let current_decl = ref None in
  let prepend lid =
    match file_of lid with
    | Some f when f <> fst file ->
        let dep = (Option.get !current_decl, fst file, lid, f) in
        Hashtbl.replace deps f dep
    | _ ->
        ()
  in
  (object
    inherit [_] iter as super
    method! visit_decl env decl =
      current_decl := Some (lid_of_decl decl);
      super#visit_decl env decl
    method! visit_EQualified _ lid =
      prepend lid
    method! visit_TQualified _ lid =
      prepend lid
    method! visit_TApp _ lid _ =
      prepend lid
  end)#visit_file () file;
  deps

let topological_sort files =
  (* We perform a dependency analysis on this set of files to figure out how to
   * order them; this is the creation of the dependency graph. Instead of merely
   * keeping a list of dependencies, we keep a hash-table that maps a dependency
   * to the [lident] that is responsible for the dependency, to have better
   * error messages. *)
  let graph = Hashtbl.create 41 in
  let file_of = mk_file_of files in
  List.iter (fun file ->
    let deps = direct_dependencies file_of file in
    Hashtbl.add graph (fst file) (ref White, deps, snd file)
  ) files;

  (* en.wikipedia.org/wiki/Topological_sorting *)
  let stack = ref [] in
  let rec dfs debug file =
    let r, deps, contents = Hashtbl.find graph file in
    match !r with
    | Black ->
        ()
    | Gray ->
        Warn.fatal_error "Bundling creates a dependency cycle:\n%s"
          (String.concat "\n" (List.map string_of_dependency debug))
    | White ->
        r := Gray;
        Hashtbl.iter (fun f dep -> dfs (dep :: debug) f) deps;
        r := Black;
        stack := (file, contents) :: !stack
  in
  List.iter (dfs []) (List.rev_map fst files);
  List.rev !stack

(* Debug any intermediary AST as follows: *)
(* PPrint.(Print.(print (PrintAst.print_files files ^^ hardline))); *)

(* This creates bundles for every [-bundle] argument that was passed on the
 * command-line. *)
let make_bundles files =
  (* We create the set of files that are either freshly-generated bundles, or
   * files that were not involved in the creation of a bundle and that,
   * therefore, we probably should keep. *)
  let used, bundles = List.fold_left (fun (used, bundles) arg ->
    let used, bundle = make_one_bundle arg files used in
    used, bundle :: bundles
  ) (StringMap.empty, []) (List.rev !Options.bundle) in
  let files = List.filter (fun (n, _) -> not (StringMap.mem n used)) files @ bundles in

  let names, _ = List.split files in
  let uniq_names = List.sort_uniq compare names in
  if List.length uniq_names <> List.length names then begin
    let seen = Hashtbl.create 42 in
    List.iter (fun name ->
      if Hashtbl.mem seen name then
        Warn.(maybe_fatal_error ("", BundleCollision name));
      Hashtbl.add seen name ()
    ) names
  end;

  (* This is important, because bundling may creates cycles, that are broken
   * after removing (now-unused) functions. *)
  let files = Inlining.drop_unused files in

  topological_sort files

(* A more refined version of direct_dependencies (found above), which
   distinguishes between internal and public dependencies. Keeps less dependency
   information, too, since it does not need to generate precise error messages.
   To be used after Inlining has run.

   We do not run this on the C grammar (which would presumably be simpler,
   because by then we would have built both flavors of headers + C files),
   because it does not distinguish between lids and ids, and also because the
   grammar is convoluted and makes it hard to access the "name" of a
   declaration.
   
   So instead, we anticipate and rely on the fact that:
   - to compute the dependencies of the public header, one needs to visit public
     (not internal, not private) functions and type declarations, and
     - skip the body of functions unless they are "static header", and
     - skip the body of type declarations marked as C abstract structs
   - to compute the dependencies of the internal header, same deal
   - to compute the dependencies of the C header, same deal except all bodies
     are visited
*)

module StringSet = Set.Make(String)
module LidSet = Idents.LidSet

type deps = {
  internal: StringSet.t;
  public: StringSet.t;
}

type all_deps = {
  h: deps;
  internal_h: deps;
  c: deps;
}

let empty_deps = { internal = StringSet.empty; public = StringSet.empty }

let drop_dinstinction { internal; public } =
  List.of_seq (StringSet.to_seq (StringSet.union internal public))

class record_everything gen_dep = object
  inherit [_] reduce
  method plus { internal = i1; public = p1 } { internal = i2; public = p2 } =
    { internal = StringSet.union i1 i2; public = StringSet.union p1 p2 }
  method zero = empty_deps
  method! visit_EQualified _ lid =
    gen_dep lid
  method! visit_TQualified _ lid =
    gen_dep lid
  method! visit_TApp () lid _ =
    gen_dep lid
end

let direct_dependencies_with_internal files file_of =
  (* Set of decls marked as internal *)
  let internal = List.fold_left (fun set (_, decls) ->
    List.fold_left (fun set decl ->
      if List.mem Common.Internal (Ast.flags_of_decl decl) then
        LidSet.add (Ast.lid_of_decl decl) set
      else
        set
    ) set decls
  ) LidSet.empty files in

  List.fold_left (fun by_file file ->
    let gen_dep (callee: lident) =
      match file_of callee with
      | Some f when f <> fst file && not (Helpers.is_primitive callee) ->
          let is_internal = LidSet.mem callee internal in
          if Options.debug "dependencies" then
            KPrint.bprintf "In file %s, reference to %a (in %sheader %s)\n"
              (fst file) PrintAst.plid callee (if is_internal then "internal " else "") f;
          if is_internal then
            { empty_deps with internal = StringSet.singleton f }
          else
            { empty_deps with public = StringSet.singleton f }
      | _ ->
          empty_deps
    in
    let is_inline_static lid = List.exists (fun p -> Bundle.pattern_matches_lid p lid) !Options.static_header in
    let header_deps which = object(self)
      inherit (record_everything gen_dep) as super

      method private concerns_us flags =
        match which with
        | `Public -> not (List.mem Common.Internal flags) && not (List.mem Common.Private flags)
        | `Internal ->  List.mem Common.Internal flags

      method! visit_DFunction env cc flags n_cgs n ret name binders body =
        (* KPrint.bprintf "function %a: concern us=%b %b %b \n" *)
        (*   PrintAst.Ops.plid name *)
        (*   (self#concerns_us flags) *)
        (*   (List.mem Common.Internal flags) (List.mem Common.Private flags); *)
        if self#concerns_us flags then
          if is_inline_static name then
            super#visit_DFunction env cc flags n_cgs n ret name binders body
          else
            (* ill-typed, but convenient *)
            super#visit_DFunction env cc flags n_cgs n ret name binders Helpers.eunit
        else
          super#zero

      method! visit_DType env name flags n_cgs n def =
        let is_c_abstract_struct = List.mem Common.AbstractStruct flags in
        if self#concerns_us flags then
          if is_c_abstract_struct then
            super#visit_DType env name flags n_cgs n (Abbrev TUnit)
          else
            super#visit_DType env name flags n_cgs n def
        else
          super#zero

      method! visit_DGlobal env flags name n t body =
        if self#concerns_us flags then
          if is_inline_static name then
            super#visit_DGlobal env flags name n t body
          else
            super#visit_DGlobal env flags name n t Helpers.eunit
        else
          super#zero
    end in
    let deps = {
      h = (
        if Options.debug "dependencies" then
          KPrint.bprintf "PUBLIC %s\n" (fst file);
        (header_deps `Public)#visit_file () file);
      internal_h = (
        if Options.debug "dependencies" then
          KPrint.bprintf "INTERNAL %s\n" (fst file);
        (header_deps `Internal)#visit_file () file);
      c = (
        if Options.debug "dependencies" then
          KPrint.bprintf "C %s\n" (fst file);
        (new record_everything gen_dep)#visit_file () file);
    } in

    if not (StringSet.is_empty deps.h.internal) then
      Warn.fatal_error "Unexpected: %s depends on some internal headers: %s\n"
        (fst file)
        (String.concat ", " (List.of_seq (StringSet.to_seq deps.h.internal)));
       
    StringMap.add (fst file) deps by_file
  ) StringMap.empty files


let debug_deps deps =
  StringMap.iter (fun name { internal; public } ->
    KPrint.bprintf "%s --> internal: %s | public: %s\n" name
      (String.concat ", " (List.of_seq (StringSet.to_seq internal)))
      (String.concat ", " (List.of_seq (StringSet.to_seq public)))
  ) deps

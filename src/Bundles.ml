(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 License. *)

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

  let mark_private =
    let add_if name flags =
      let is_private = List.mem Common.Private flags in
      if not is_private && not (Inlining.always_live name) then begin
        if List.length api > 0 then
          Hashtbl.add Inlining.marked_private name ();
        Common.Private :: flags
      end else
        flags
    in
    function
    | DFunction (cc, flags, n, typ, name, binders, body) ->
        DFunction (cc, add_if name flags, n, typ, name, binders, body)
    | DGlobal (flags, name, n, typ, body) ->
        DGlobal (add_if name flags, name, n, typ, body)
    | DType (lid, flags, n, def) ->
        DType (lid, add_if lid flags, n, def)
    | DExternal (cc, flags, lid, t, pp) ->
        DExternal (cc, add_if lid flags, lid, t, pp)
  in

  (* Match a file against the given list of patterns. *)
  let match_file is_api patterns (used, found) (file: file) =
    List.fold_left (fun (used, found) pattern ->
      let name = fst file in
      (* [is_api] overrides the default behavior (don't collect) *)
      if pattern_matches pattern name && (is_api || not (in_api_list name)) then begin
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
          Suggestion #1: if the file does exist, pass it to KreMLin.\n\
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
        let dep = (Option.must !current_decl, fst file, lid, f) in
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

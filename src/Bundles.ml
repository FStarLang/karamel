(** Collapsing several F* modules into a single "bundle" to allow more static
 * uses. *)

open Bundle
open Ast

module StringMap = Map.Make(String)

let parse = Utils.parse Parser.bundle

(** A given pattern matches an F* filename (i.e. a string using the underscore
 * as a separator *)
let pattern_matches (p: Bundle.pat) (m: string) =
  match p with
  | Module m' ->
      String.concat "_" m' = m
  | Prefix p ->
      KString.starts_with m (String.concat "_" p ^ "_")

let bundle_name (api, patterns) =
  match api with
  | [] ->
      String.concat "_" (KList.map_flatten (function
        | Module m -> m
        | Prefix p -> p
      ) patterns)
  | _ ->
     String.concat "_" api

let uniq =
  let r = ref 0 in
  fun () ->
    incr r;
    !r

(** This collects all the files that match a given bundle specification, while
 * preserving their original dependency ordering within the bundle. If the
 * bundle is of the form Api=Patterns, then the declarations from Api are kept
 * as-is, while declarations from the modules that match the Patterns are marked
 * as private. Assuming no cross-translation-unit calls happen, this means a C
 * static qualifier in the extracted code.
 *
 * The used parameter is just here to keep track of which files have been
 * involved in at least one bundle, so that we can drop them afterwards. *)
let make_one_bundle (bundle: Bundle.t) (files: file list) (used: int StringMap.t) =
  let debug = Options.debug "bundle" in
  if debug then
    KPrint.bprintf "Starting creation of bundle %s\n" (bundle_name bundle);

  let api, patterns = bundle in
  (* The used map also allows us to detect when a file is used twice in a
   * bundle. *)
  let this_round = uniq () in

  (* Match a file against the given list of patterns. *)
  let match_file is_api patterns (used, found) file =
    List.fold_left (fun (used, found) pattern ->
      let name = fst file in
      if pattern_matches pattern name && (is_api || name <> String.concat "_" api) then begin
        if debug then
          KPrint.bprintf "%s is a match\n" name;

        (* Be nice and give an error. *)
        let prev_round = try StringMap.find name used with Not_found -> 0 in
        if prev_round = this_round then
          Warnings.fatal_error "The file %s is matched twice by bundle %s\n"
            name (string_of_bundle bundle);

        StringMap.add name this_round used, file :: found
      end else begin
        used, found
      end
    ) (used, found) patterns
  in

  (* Find all the files that match the given patterns. *)
  let used, found = List.fold_left (match_file false patterns) (used, []) files in

  (* All the declarations that have matched the patterns are marked as private. *)
  let found = List.map (fun (old_name, decls) ->
    old_name, List.map (function 
      | DFunction (cc, flags, n, typ, name, binders, body) ->
          DFunction (cc, Common.Private :: flags, n, typ, name, binders, body)
      | DGlobal (flags, name, typ, body) ->
          DGlobal (Common.Private :: flags, name, typ, body)
      | decl ->
          decl
    ) decls
  ) found in

  (* The Api module gets a special treatment; if it exists, it is not collected
   * in the call to [fold_left] above; rather, it is taken now from the list of
   * files so that its declarations do not get the special "private" treatment. *)
  let used, found =
    if api = [] then
      used, found
    else
      let count = StringMap.cardinal used in
      if debug then
        KPrint.bprintf "Looking for bundle API\n";
      let used, found = List.fold_left (match_file true [ Module api ]) (used, found) files in
      if StringMap.cardinal used <> count + 1 then
        Warnings.fatal_error "There an issue with your bundle.\n\
          You specified: -bundle %s=...\n\
          Here's the issue: there is no module named %s.\n\
          Suggestion #1: if the file does exist, pass it to KreMLin.\n\
          Suggestion #2: if it doesn't, skip the %s= part and write -bundle ..."
          (String.concat "." api)
          (String.concat "." api)
          (String.concat "." api);
      used, found
  in

  (* We return the updated map of all "used" original files *)
  let bundle = bundle_name bundle, List.flatten (List.rev_map snd found) in
  used, bundle

type color = White | Gray | Black

type dependency = lident * string * lident * string

let string_of_dependency (d1, f1, d2, f2) =
  KPrint.bsprintf "%a (found in file %s) mentions %a (found in file %s)"
    PrintAst.plid d1 f1 PrintAst.plid d2 f2

(* This creates bundles for every [-bundle] argument that was passed on the
 * command-line. *)
let make_bundles files =
  (* We create the set of files that are either freshly-generated bundles, or
   * files that were not involved in the creation of a bundle and that,
   * therefore, we probably should keep. *)
  let used, bundles = List.fold_left (fun (used, bundles) arg ->
    let used, bundle = make_one_bundle arg files used in
    used, bundle :: bundles
  ) (StringMap.empty, []) !Options.bundle in
  let files = List.filter (fun (n, _) -> not (StringMap.mem n used)) files @ bundles in

  (* This is important, because bundling may creates cycles, that are broken
   * after removing (now-unused) functions. *)
  let files = Inlining.drop_unused files in

  (* We perform a dependency analysis on this set of files to figure out how to
   * order them; this is the creation of the dependency graph. Instead of merely
   * keeping a list of dependencies, we keep a hash-table that maps a dependency
   * to the [lident] that is responsible for the dependency, to have better
   * error messages. *)
  let graph = Hashtbl.create 41 in
  let file_of = mk_file_of files in
  List.iter (fun file ->
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
    ignore ((object
      inherit [unit] map as super
      method visit_d env decl =
        current_decl := Some (lid_of_decl decl);
        super#visit_d env decl
      method equalified _ _ lid =
        prepend lid;
        EQualified lid
      method tqualified _ lid =
        prepend lid;
        TQualified lid
    end)#visit_file () file);
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
        Warnings.fatal_error "Bundling creates a dependency cycle:\n%s"
          (String.concat "\n" (List.map string_of_dependency debug))
    | White ->
        r := Gray;
        Hashtbl.iter (fun f dep -> dfs (dep :: debug) f) deps;
        r := Black;
        stack := (file, contents) :: !stack
  in
  List.iter (dfs []) (List.map fst files);

  let palatable_dependencies =
    Hashtbl.fold (fun file (_, deps, _) acc ->
      (file, Hashtbl.fold (fun f _ acc -> f :: acc) deps []) :: acc
    ) graph []
  in

  if Options.debug "dependencies" then
    List.iter (fun (f, deps) ->
      KPrint.bprintf "%s: %s\n" f (String.concat " " deps)
    ) palatable_dependencies;

  List.rev !stack, palatable_dependencies

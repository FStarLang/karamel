(** Collapsing several F* modules into a single "bundle" to allow more static
 * uses. *)

open Bundle
open Ast

module StringMap = Map.Make(String)

let parse arg =
  let the_parser = MenhirLib.Convert.Simplified.traditional2revised Parser.bundle in
  let lexbuf = Ulexing.from_utf8_string arg in
  try
    the_parser (fun _ -> Lexer.token lexbuf)
  with Ulexing.Error | Parser.Error ->
    Warnings.fatal_error "Malformed bundle"

let debug = false

(** This collects all the files that match a given bundle specification, while
 * preserving their original dependency ordering within the bundle. If the
 * bundle is of the form Api=Patterns, then the declarations from Api are kept
 * as-is, while declarations from the modules that match the Patterns are marked
 * as private. Assuming no cross-translation-unit calls happen, this means a C
 * static qualifier in the extracted code. *)
let make_one_bundle (bundle: Bundle.t) (files: file list) (used: bool StringMap.t) =
  let api, patterns = bundle in
  (* Find the files that match a given pattern *)
  let find_files is_api (used, found) pattern =
    List.fold_left (fun (used, found) file ->
      let name = fst file in
      match pattern with
      | Module m when String.concat "_" m = name &&
        (is_api || name <> String.concat "_" api) ->
          StringMap.add name true used, file :: found
      | Prefix p when KString.starts_with name (String.concat "_" p) &&
        (is_api || name <> String.concat "_" api) ->
          StringMap.add name true used, file :: found
      | _ ->
          used, found
    ) (used, found) files
  in
  (* Find all the files that match the given patterns. *)
  (* FIXME: this assumes that the patterns are non-overlapping. *)
  let used, found = List.fold_left (find_files false) (used, []) patterns in
  (* All the declarations that have matched the patterns are marked as private. *)
  let found = List.map (fun (old_name, decls) ->
    old_name, List.map (function 
      | DFunction (cc, flags, typ, name, binders, body) ->
          DFunction (cc, Common.Private :: flags, typ, name, binders, body)
      | DGlobal (flags, name, typ, body) ->
          DGlobal (Common.Private :: flags, name, typ, body)
      | decl ->
          decl
    ) decls
  ) found in
  (* The Api module gets a special treatment; if it exists, it is not collected
   * in the call to [fold_left] above; rather, it is taken now from the list of
   * files so that its declarations do not get the special "private" treatment. *)
  let used, found = find_files true (used, found) (Module api) in
  (* The name of the bundle is the name of the Api module *)
  let bundle = String.concat "_" api, List.flatten (List.rev_map snd found) in
  (* We return the updated map of all "used" original files *)
  used, bundle

type color = White | Gray | Black

module LidMap = Idents.LidMap

(* Create a map from an lid to the file it now appears in (after bundling).
 * FIXME we should take this as an opportunity to flag bundling errors, i.e.
 * there's a cross-compilation-unit dependency on a function that is defined in
 * several bundles... *)
let mk_file_of files =
  let file_of = List.fold_left (fun map (name, decls) ->
    List.fold_left (fun map decl ->
      LidMap.add (lid_of_decl decl) name map
    ) map decls
  ) LidMap.empty files in
  let file_of lid =
    try
      Some (LidMap.find lid file_of)
    with Not_found ->
      None
  in
  file_of

(* This creates bundles for every [-bundle] argument that was passed on the
 * command-line. *)
let make_bundles files =
  if debug then
    KPrint.bprintf "List of files: %s\n" (String.concat " " (List.map fst files));

  (* We create the set of files that are either freshly-generated bundles, or
   * files that were not involved in the creation of a bundle and that,
   * therefore, we probably should keep. *)
  let used, bundles = List.fold_left (fun (used, bundles) arg ->
    let used, bundle = make_one_bundle arg files used in
    used, bundle :: bundles
  ) (StringMap.empty, []) !Options.bundle in
  let files = List.filter (fun (n, _) -> not (StringMap.mem n used)) files @ bundles in

  if debug then begin
    KPrint.bprintf "List of files used in bundling: %s\n"
      (String.concat " " (StringMap.fold (fun k _ acc -> k :: acc) used []));
    KPrint.bprintf "List of files after bundling: %s\n" (String.concat " " (List.map fst files));
  end;

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
          Hashtbl.replace deps f (Option.must !current_decl)
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
        Warnings.fatal_error "Bundling creates a dependency cycle: %s"
          (String.concat " <- " (List.map Idents.string_of_lident debug))
    | White ->
        r := Gray;
        Hashtbl.iter (fun f lid -> dfs (lid :: debug) f) deps;
        r := Black;
        stack := (file, contents) :: !stack
  in
  List.iter (dfs []) (List.map fst files);
  List.rev !stack

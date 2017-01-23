(** Collapsing several F* modules into a single "bundle" to allow more static
 * uses. *)

open Bundle
open Ast

module StringMap = Map.Make(String)

let debug = false

(** Returns a single file that is the result of bundling several other files,
 * possibly with extra private flags added depending on whether the bundle name
 * matches an existing file or not. We do not perform renamings.
 * TODO: figure out what happens with the checker when it sees multiple bindings
 * that have the same name *)
let make_one_bundle (bundle: Bundle.t) (files: file list) (used: bool StringMap.t) =
  let api, patterns = bundle in
  let find_file is_api (used, found) pattern =
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
  let used, found = List.fold_left (find_file false) (used, []) patterns in
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
  let used, found = find_file true (used, found) (Module api) in
  let bundle = String.concat "_" api, List.flatten (List.rev_map snd found) in
  used, bundle

type color = White | Gray | Black

let parse_arg arg =
  let the_parser = MenhirLib.Convert.Simplified.traditional2revised Parser.bundle in
  let lexbuf = Ulexing.from_utf8_string arg in
  try
    the_parser (fun _ -> Lexer.token lexbuf)
  with Ulexing.Error | Parser.Error ->
    Warnings.fatal_error "Malformed bundle"

let make_bundles files =
  if debug then
    KPrint.bprintf "List of files: %s\n" (String.concat " " (List.map fst files));
  let used, bundles = List.fold_left (fun (used, bundles) arg ->
    let used, bundle = make_one_bundle (parse_arg arg) files used in
    used, bundle :: bundles
  ) (StringMap.empty, []) !Options.bundle in
  let files = List.filter (fun (n, _) -> not (StringMap.mem n used)) files @ bundles in
  if debug then begin
    KPrint.bprintf "List of files used in bundling: %s\n"
      (String.concat " " (StringMap.fold (fun k _ acc -> k :: acc) used []));
    KPrint.bprintf "List of files after bundling: %s\n" (String.concat " " (List.map fst files));
  end;

  let graph = Hashtbl.create 41 in
  List.iter (fun file ->
    let deps = Hashtbl.create 41 in
    let current_decl = ref None in
    let prepend lid =
      let f = String.concat "_" (fst lid) in
      (* Don't take self-dependencies *)
      if f <> (fst file) then
        Hashtbl.replace deps f (Option.must !current_decl)
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

  let stack = ref [] in
  let rec dfs debug file =
    match Hashtbl.find graph file with
    | exception Not_found ->
        (* This refers to a now-gone module that ended up in a bundle *)
        ()
    | r, deps, contents ->
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

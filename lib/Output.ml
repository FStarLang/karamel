(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 and MIT Licenses. *)

(** Decorate each file with a little bit of boilerplate, then print it *)

open Utils
open PPrint

type which = H | InternalH | C

let mk_includes =
  separate_map hardline (fun x -> string "#include " ^^ string x)

let filter_includes which file (includes: (Options.include_ * string) list) =
  (* KPrint.bprintf "-- filter_includes for %s (%d)\n" file (List.length includes); *)
  KList.filter_some (List.rev_map (function
    | Options.HeaderOnly file', h when file = file' && which = H ->
        (* KPrint.bprintf "--- H Match %s: include %s\n" file h; *)
        Some h
    | InternalOnly file', h when file = file' && which = InternalH ->
        (* KPrint.bprintf "--- H Match %s: include %s\n" file h; *)
        Some h
    | COnly file', h when file = file' && which = C->
        (* KPrint.bprintf "--- C Match %s: include %s\n" file h; *)
        Some h
    | All, h when which = H || which = InternalH ->
        (* KPrint.bprintf "--- All Match %s: include %s\n" file h; *)
        Some h
    | _i, _h ->
        (* KPrint.bprintf "--- No match for %s: -add-include %a:%s (is_c: %b)\n" *)
        (*   file Options.pinc _i _h is_c; *)
        None
  ) includes)

let krmllib_include () =
  if !Options.minimal then
    empty
  else
    mk_includes [ "\"krmllib.h\"" ] ^^ hardline ^^ hardline

(* A Pprint document with:
 * - #include X for X in the dependencies of the file, followed by
 * - #include Y for each -add-include Y passed on the command-line
 *)
let includes_for which file files =
  let extra_includes = filter_includes which file !Options.add_include in
  let includes = List.rev_map (Printf.sprintf "\"%s.h\"") files in
  let includes = includes @ extra_includes in
  if includes = [] then
    empty
  else
    mk_includes includes ^^ hardline ^^ hardline

let early_includes_for which file =
  let includes = filter_includes which file !Options.add_early_include in
  if includes = [] then
    empty
  else
    mk_includes includes ^^ hardline ^^ hardline

let invocation (): string =
  KPrint.bsprintf
{|
  This file was generated by KaRaMeL <https://github.com/FStarLang/karamel>
  KaRaMeL invocation: %s
  F* version: %s
  KaRaMeL version: %s
|}
    (String.concat " " (Array.to_list Sys.argv))
    !Driver.fstar_rev
    !Driver.krml_rev

let header (): string =
  let default = invocation () in
  if !Options.header = "" then
    "/* " ^ default ^ " */"
  else
    let fmt = Utils.file_get_contents !Options.header in
    try
      let fmt = Scanf.format_from_string fmt "%s" in
      KPrint.bsprintf fmt default
    with Scanf.Scan_failure _ ->
      fmt

(* A pair of a header, containing:
 * - the boilerplate specified on the command-line by -header
 * - #include Y for each -add-early-include Y passed on the command-line
 * - #include "krmllib.h"
 * - the #ifndef #define guard,
 * and a footer, containing:
 * - the #endif
 *)
let prefix_suffix which original_name name =
  Driver.detect_fstar_if ();
  Driver.detect_karamel_if ();
  let if_cpp doc =
    string "#if defined(__cplusplus)" ^^ hardline ^^
    doc ^^ hardline ^^
    string "#endif" ^^ hardline
  in
  let macro_name = String.map (function '/' -> '_' | c -> c) name in
  (* KPrint.bprintf "- add_early_includes: %s\n" original_name; *)
  let prefix =
    string (header ()) ^^ hardline ^^ hardline ^^
    string (Printf.sprintf "#ifndef __%s_H" macro_name) ^^ hardline ^^
    string (Printf.sprintf "#define __%s_H" macro_name) ^^ hardline ^^
    (if !Options.extern_c then hardline ^^ if_cpp (string "extern \"C\" {") else empty) ^^
    hardline ^^
    early_includes_for which original_name ^^
    krmllib_include ()
  in
  let suffix =
    hardline ^^
    (if !Options.extern_c then if_cpp (string "}") else empty) ^^ hardline ^^
    string (Printf.sprintf "#define __%s_H_DEFINED" macro_name) ^^ hardline ^^
    string "#endif"
  in
  prefix, suffix

let in_tmp_dir name =
  let open Driver in
  if !Options.tmpdir <> "" then
    !Options.tmpdir ^^ name
  else
    name

let write_one name prefix program suffix =
  with_open_out_bin (in_tmp_dir name) (fun oc ->
    let doc =
      prefix ^^
      separate_map (hardline ^^ hardline) PrintC.p_decl_or_function program ^^
      hardline ^^
      suffix ^^ hardline
    in
    PPrint.ToChannel.pretty 0.95 100 oc doc
  )

let create_subdir d =
  if !Options.tmpdir = "" then
    Driver.mkdirp d
  else
    Driver.mkdirp (!Options.tmpdir ^ "/" ^ d)

let maybe_create_internal_dir h =
  if List.exists (function (_, C11.Internal _) -> true | _ -> false) h then
    create_subdir "internal"

let write_c files internal_headers (deps: Bundles.all_deps Bundles.StringMap.t) =
  Driver.detect_fstar_if ();
  Driver.detect_karamel_if ();
  List.map (fun file ->
    let name, program = file in
    let all_deps = Bundles.StringMap.find name deps in
    let internal_deps = List.of_seq (Bundles.StringSet.to_seq all_deps.Bundles.c.Bundles.internal) in
    let public_deps = List.of_seq (Bundles.StringSet.to_seq all_deps.Bundles.c.Bundles.public) in
    let deps = List.map (fun f -> "internal/" ^ f) internal_deps @ public_deps in
    let includes = includes_for C name deps in
    let header = string (header ()) ^^ hardline ^^ hardline in
    let internal = if Bundles.StringSet.mem name internal_headers then "internal/" else "" in
    (* If there is an internal header, we include that rather than the public
       one. The internal header always includes the public one. *)
    let my_h = string (Printf.sprintf "#include \"%s%s.h\"" internal name) in
    let prefix =
      header ^^
      early_includes_for C name ^^
      (if !Options.add_include_tmh then
        string "#ifdef WPP_CONTROL_GUIDS" ^^ hardline ^^
        string (Printf.sprintf "#include <%s.tmh>" name) ^^ hardline ^^
        string "#endif" ^^ hardline
      else
        empty) ^^
      my_h ^^ hardline ^^ hardline ^^
      includes
    in
    write_one (name ^ ".c") prefix program empty;
    name
  ) files

let write_h files public_headers (deps: Bundles.all_deps Bundles.StringMap.t) =
  List.map (fun file ->
    let name, program = file in
    let all_deps = Bundles.StringMap.find name deps in
    let { Bundles.public; internal } = match program with
      | C11.Internal _ -> all_deps.Bundles.internal_h
      | C11.Public _ -> all_deps.Bundles.h
    in
    let public = List.of_seq (Bundles.StringSet.to_seq public) in
    let internal = List.of_seq (Bundles.StringSet.to_seq internal) in
    let original_name = name in
    let name, program, deps, which =
      match program with
      | C11.Internal h ->
          (* Internal header depends on public header + other internal headers.
           The "../" is annoying but otherwise this ends up resolving to the
           internal header in the current (internal) directory.
           TODO: figure out whether karamel should generate includes with <...>? *)
          let internal_headers = List.map (fun f -> "internal/" ^ f) internal in
          let headers =
            if Bundles.StringSet.mem name public_headers then
              ("../" ^ name) :: public @ internal_headers
            else
              public @ internal_headers
          in
          "internal/" ^ name, h, headers, InternalH
      | C11.Public h ->
          name, h, public, H
    in
    (* KPrint.bprintf "- write_h: %s\n" name; *)
    let includes = includes_for which original_name deps in
    let prefix, suffix = prefix_suffix which original_name name in
    write_one (name ^ ".h") (prefix ^^ includes) program suffix;
    name
  ) files

let write_makefile user_ccopts custom_c_files c_files h_files =
  let concat_map ext files =
    String.concat " " (List.map (fun f -> f ^ ext) files)
  in
  Utils.with_open_out_bin (in_tmp_dir "Makefile.include") (fun oc ->
    KPrint.bfprintf oc "USER_TARGET=%s\n" !Options.exe_name;
    KPrint.bfprintf oc "USER_CFLAGS=%s\n" (concat_map "" (List.rev user_ccopts));
    KPrint.bfprintf oc "USER_C_FILES=%s\n" (concat_map "" (List.sort compare custom_c_files));
    KPrint.bfprintf oc "ALL_C_FILES=%s\n" (concat_map ".c" (List.sort compare c_files));
    KPrint.bfprintf oc "ALL_H_FILES=%s\n" (concat_map ".h" (List.sort compare h_files))
  );
  Utils.cp Driver.(!Options.tmpdir ^^ "Makefile.basic") Driver.(!misc_dir ^^ "Makefile.basic")

let write_def m c_files =
  let dst = in_tmp_dir (Filename.chop_extension !Options.exe_name ^ ".def") in
  with_open_out_bin dst (fun oc ->
    KPrint.bfprintf oc "LIBRARY %s\n\nEXPORTS\n"
      (Filename.basename (Filename.chop_extension !Options.exe_name));
    List.iter (fun (_, decls) ->
      List.iter (function
        | Ast.DFunction (_, flags, _, _, _, name, _, _)
          when not (List.mem Common.Private flags) ->
            let name = GlobalNames.to_c_name m name in
            KPrint.bfprintf oc "  %s\n" name
        | _ -> ()
      ) decls
    ) c_files
  )

let write_renamings (m: GlobalNames.mapping) =
  create_subdir "clients";
  let dst = in_tmp_dir "clients/krmlrenamings.h" in
  with_open_out_bin dst (fun oc ->
    Hashtbl.iter (fun original_name (new_name, non_modular_renaming) ->
      (* Note: there is a slight imprecision here. If the original name WOULD
         HAVE BEEN renamed because of a name collision, then this renaming map
         will be incorrect. We would to track two maps in GlobalNames, the
         actual one, and the "sans the renamings" one, in order to be accurate.
         Too much work, unlikely to happen. *)
      if non_modular_renaming then
        KPrint.bfprintf oc "#define %s %s\n" (Idents.string_of_lident original_name) new_name)
    m)

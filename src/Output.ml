(** Decorate each file with a little bit of boilerplate, then print it *)

open Utils
open PPrint

let mk_includes =
  separate_map hardline (fun x -> string "#include " ^^ string x) 

let kremlib_include =
  if !Options.minimal then
    empty
  else
    mk_includes [ "\"kremlib.h\"" ]

(* A Pprint document with:
 * - #include X for X in the dependencies of the file, followed by
 * - #include Y for each -add-include Y passed on the command-line
 *)
let includes files =
  let extra_includes = mk_includes (List.rev !Options.add_include) in
  let includes = mk_includes (List.rev_map (Printf.sprintf "\"%s.h\"") files) in
  includes ^^ hardline ^^ extra_includes

(* A pair of a header, containing:
 * - the boilerplate specified on the command-line by -header
 * - #include Y for each -add-early-include Y passed on the command-line
 * - #include "kremlib.h"
 * - the #ifndef #define guard,
 * and a footer, containing:
 * - the #endif
 *)
let prefix_suffix name =
  let prefix =
    string !Options.header ^^ hardline ^^
    mk_includes !Options.add_early_include ^^
    kremlib_include ^^
    hardline ^^
    string (Printf.sprintf "#ifndef __%s_H" name) ^^ hardline ^^
    string (Printf.sprintf "#define __%s_H" name) ^^ hardline
  in
  prefix, string "#endif"

let write_one name prefix program suffix =
  Driver.mk_tmpdir_if ();
  let f =
    let open Driver in
    if !Options.tmpdir <> "" then
      !Options.tmpdir ^^ name
    else
      name
  in
  with_open_out f (fun oc ->
    let doc =
      prefix ^^ hardline ^^ hardline ^^
      separate_map (hardline ^^ hardline) PrintC.p_decl_or_function program ^^
      hardline ^^ suffix ^^ hardline
    in
    PPrint.ToChannel.pretty 0.95 100 oc doc
  )

let write_c files =
  ignore (List.fold_left (fun names file ->
    let name, program = file in
    let prefix = string (Printf.sprintf "%s\n\n#include \"%s.h\"" !Options.header name) in
    write_one (name ^ ".c") prefix program empty;
    name :: names
  ) [] files)

let write_h files =
  ignore (List.fold_left (fun names file ->
    let name, program = file in
    let prefix, suffix = prefix_suffix name in
    let prefix = prefix ^^ hardline ^^ includes names in
    write_one (name ^ ".h") prefix program suffix;
    name :: names
  ) [] files)

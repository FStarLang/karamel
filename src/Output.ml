(** Decorate each file with a little bit of boilerplate, then print it *)

open Utils
open PPrint

let includes files =
  let extra_includes = separate_map hardline
    (fun x -> string "#include " ^^ string x) (List.rev !Options.add_include)
  in
  let includes = separate_map hardline (fun i ->
    string "#include " ^^ dquote ^^ string i ^^ string ".h" ^^ dquote
  ) (List.rev files) in
  includes ^^ hardline ^^ extra_includes

let header name =
  let header = !Options.header in
  let prefix = string (Printf.sprintf
{|%s
#include "kremlib.h"
#ifndef __%s_H
#define __%s_H
|} header name name) in
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
    let prefix, suffix = header name in
    let prefix = prefix ^^ hardline ^^ hardline ^^ includes names in
    write_one (name ^ ".h") prefix program suffix;
    name :: names
  ) [] files)

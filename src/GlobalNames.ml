(** All global names must be valid C identifiers and globally-unique... *)

open Warnings
open Idents

let c_of_original = Hashtbl.create 41
let used_c_names: (string, unit) Hashtbl.t = Hashtbl.create 41

let record original_name desired_name =
  match Hashtbl.find c_of_original original_name with
  | exception Not_found ->
      let unique_c_name = mk_fresh desired_name (Hashtbl.mem used_c_names) in
      Hashtbl.add c_of_original original_name unique_c_name;
      Hashtbl.add used_c_names unique_c_name ();
      unique_c_name
  | x ->
      if true then x else
      fatal_error "Duplicate global name: %s" original_name

let translate name fallback =
  try
    Hashtbl.find c_of_original name
  with Not_found ->
    (* Assuming some externally-realized function. *)
    to_c_identifier fallback

let _ =
  let keywords = [
    "auto";
    "break";
    "case";
    "char";
    "const";
    "continue";
    "default";
    "do";
    "double";
    "else";
    "enum";
    "extern";
    "float";
    "for";
    "goto";
    "if";
    "inline";
    "int";
    "long";
    "register";
    "restrict";
    "return";
    "short";
    "signed";
    "sizeof";
    "static";
    "struct";
    "switch";
    "typedef";
    "union";
    "unsigned";
    "void";
    "volatile";
    "while";
    "_Alignas";
    "_Alignof";
    "_Atomic";
    "_Bool";
    "_Complex";
    "_Generic";
    "_Imaginary";
    "_Noreturn";
    "_Static_assert";
    "_Thread_local";
    "_Pragma";
    "asm";
    "fortran"
  ] in
  List.iter (fun k -> Hashtbl.add used_c_names k ()) keywords

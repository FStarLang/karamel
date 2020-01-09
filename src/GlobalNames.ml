(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 License. *)

(** All global names must be valid C identifiers and globally-unique... *)

open Warn
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
  | _ ->
      fatal_error "Duplicate global name: %s" original_name

let translate name fallback =
  try
    Hashtbl.find c_of_original name
  with Not_found ->
    (* Assuming some externally-realized function. *)
    to_c_identifier fallback

let _ =
  let keywords = [
    "_Alignas";
    "_Alignof";
    "_Atomic";
    "_Bool";
    "_Complex";
    "_Generic";
    "_Imaginary";
    "_Noreturn";
    "_Pragma";
    "_Static_assert";
    "_Thread_local";
    "alignas";
    "alignof";
    "and";
    "and_eq";
    "asm";
    "atomic_cancel";
    "atomic_commit";
    "atomic_noexcept";
    "auto";
    "bitand";
    "bitor";
    "bool";
    "break";
    "case";
    "catch";
    "char";
    "char16_t";
    "char32_t";
    "char8_t";
    "class";
    "co_await";
    "co_return";
    "co_yield";
    "compl";
    "concept";
    "const";
    "const_cast";
    "consteval";
    "constexpr";
    "constinit";
    "continue";
    "decltype";
    "default";
    "delete";
    "do";
    "double";
    "dynamic_cast";
    "else";
    "enum";
    "explicit";
    "export";
    "extern";
    "false";
    "float";
    "for";
    "fortran";
    "friend";
    "goto";
    "if";
    "inline";
    "int";
    "long";
    "mutable";
    "namespace";
    "new";
    "noexcept";
    "not";
    "not_eq";
    "nullptr";
    "operator";
    "or";
    "or_eq";
    "private";
    "protected";
    "public";
    "reflexpr";
    "register";
    "reinterpret_cast";
    "requires";
    "restrict";
    "return";
    "short";
    "signed";
    "sizeof";
    "static";
    "static_assert";
    "static_cast";
    "struct";
    "switch";
    "synchronized";
    "template";
    "this";
    "thread_local";
    "throw";
    "true";
    "try";
    "typedef";
    "typeid";
    "typename";
    "union";
    "unsigned";
    "using";
    "virtual";
    "void";
    "volatile";
    "wchar_t";
    "while";
    "xor";
    "xor_eq";
  ] in
  List.iter (fun k -> Hashtbl.add used_c_names k ()) keywords

(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 License. *)

(** All global names must be valid C identifiers and globally-unique... *)

open Warn
open Idents
open Ast
open PrintAst.Ops

type mapping = (lident, string) Hashtbl.t
type t = mapping * (string, unit) Hashtbl.t

let dump (env: t) =
  Hashtbl.iter (fun lident c_name ->
    KPrint.bprintf "%a --> %s\n" plid lident c_name
  ) (fst env);
  Hashtbl.iter (fun c_name _ ->
    KPrint.bprintf "%s is used\n" c_name
  ) (snd env)

let reserve_keywords used_c_names =
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
  List.iter (fun k -> Hashtbl.add used_c_names k ()) keywords;
  (* Some stuff that's already almost always in scope. *)
  let std = [
    "errno"
  ] in
  List.iter (fun k -> Hashtbl.add used_c_names k ()) std

let create () =
  let c_of_original = Hashtbl.create 41 in
  let used_c_names: (string, unit) Hashtbl.t = Hashtbl.create 41 in
  reserve_keywords used_c_names;
  c_of_original, used_c_names

let extend (global: t) (local: t) is_local original_name desired_name =
  let c_of_original, g_used_c_names = global in
  let _, l_used_c_names = local in
  if Hashtbl.mem c_of_original original_name then
    fatal_error "Duplicate global name: %a" plid original_name;

  let unique_c_name = mk_fresh desired_name (fun x ->
    Hashtbl.mem g_used_c_names x || Hashtbl.mem l_used_c_names x) in
  Hashtbl.add c_of_original original_name unique_c_name;
  if is_local then
    Hashtbl.add l_used_c_names unique_c_name ()
  else
    Hashtbl.add g_used_c_names unique_c_name ();
  unique_c_name

let lookup (env: t) name =
  let c_of_original, _ = env in
  Hashtbl.find_opt c_of_original name

let clone (env: t) =
  let c_of_original, used_c_names = env in
  Hashtbl.copy c_of_original, Hashtbl.copy used_c_names

let mapping = fst

let skip_prefix lid =
  List.exists (fun p -> Helpers.pattern_matches p lid) !Options.no_prefix

(* Because of dedicated treatment in CStarToC11 *)
let ineligible lident =
  List.mem (fst lident) [
    ["FStar"; "UInt128"];
    ["C"; "Nullity"];
    ["C"; "String"];
    ["C"; "Compat"; "String"];
    ["LowStar"; "BufferOps"];
    ["LowStar"; "Buffer"];
    ["LowStar"; "Monotonic"; "Buffer"]
  ]

let bundle_matches (apis, patterns, _) lid =
  List.mem (fst lid) apis ||
  List.exists (fun p -> Helpers.pattern_matches p lid) patterns

let rename_prefix lid =
  KList.find_opt (fun b ->
    if List.mem Bundle.RenamePrefix (Bundle.attrs_of_bundle b) && bundle_matches b lid then
      Some (Bundle.bundle_filename b)
    else
      None
  ) !Options.bundle

let pascal_case name =
  let module T = struct type what = | Keep | Up | Low end in
  let has_underscore = String.contains name '_' in
  if has_underscore then
    let b = Buffer.create 256 in
    let what_next = ref T.Up in
    for i = 0 to String.length name - 1 do
      match name.[i] with
      | '_' ->
          what_next := T.Up
      | c ->
          let c_next = match !what_next with
            | T.Keep -> c
            | T.Up -> Char.uppercase c
            | T.Low -> Char.lowercase c
          in
          if Char.uppercase c = c then
            what_next := T.Low
          else if Char.lowercase c = c then
            what_next := T.Keep;
          Buffer.add_char b c_next
    done;
    Buffer.contents b
  else
    String.uppercase (String.sub name 0 1) ^ 
    String.sub name 1 (String.length name - 1)

let camel_case name =
  let name = pascal_case name in
  String.lowercase (String.sub name 0 1) ^ 
  String.sub name 1 (String.length name - 1)

let strip_leading_underscores name =
  let i = ref 0 in
  while name.[!i] = '_' do incr i done;
  if !i = String.length name then
    failwith "cannot have a name made of a single underscore";
  String.sub name !i (String.length name - !i)

let target_c_name ~attempt_shortening ~is_macro lid =
  let pre_name =
    if skip_prefix lid && not (ineligible lid) then
      snd lid
    else if attempt_shortening && not (ineligible lid) && snd lid <> "main" then
      snd lid
    else match rename_prefix lid with
    | Some prefix ->
        prefix ^ "_" ^ snd lid
    | None ->
        string_of_lident lid
  in
  if !Options.microsoft && not is_macro && pre_name <> "main" then
    pascal_case pre_name
  else if !Options.microsoft && is_macro then
    strip_leading_underscores pre_name
  else
    pre_name

let to_c_name m lid =
  try
    Hashtbl.find m lid
  with Not_found ->
    Idents.to_c_identifier (target_c_name ~attempt_shortening:false ~is_macro:false lid)


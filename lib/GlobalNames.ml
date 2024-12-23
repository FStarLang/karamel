(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 and MIT Licenses. *)

(** All global names must be valid C identifiers and globally-unique... *)

open Warn
open Idents
open Ast
open PrintAst.Ops

type mapping = (lident, string * bool) Hashtbl.t
type t = mapping * (string, unit) Hashtbl.t

let dump (env: t) =
  Hashtbl.iter (fun lident (c_name, nm) ->
    KPrint.bprintf "%a --> %s%s\n" plid lident c_name (if nm then " (!)" else "")
  ) (fst env);
  Hashtbl.iter (fun c_name _ ->
    KPrint.bprintf "%s is used\n" c_name
  ) (snd env)

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
]

let reserve_keywords used_c_names =
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

let extend (global: t) (local: t) is_local original_name (desired_name, non_modular_renaming) =
  let c_of_original, g_used_c_names = global in
  let _, l_used_c_names = local in
  if Hashtbl.mem c_of_original original_name then
    fatal_error "Duplicate global name: %a" plid original_name;

  let unique_c_name = mk_fresh desired_name (fun x ->
    Hashtbl.mem g_used_c_names x || Hashtbl.mem l_used_c_names x) in
  Hashtbl.add c_of_original original_name (unique_c_name, non_modular_renaming && not is_local);
  if is_local then
    Hashtbl.add l_used_c_names unique_c_name ()
  else
    Hashtbl.add g_used_c_names unique_c_name ();
  unique_c_name

let lookup (env: t) name =
  let c_of_original, _ = env in
  Option.map fst (Hashtbl.find_opt c_of_original name)

let clone (env: t) =
  let c_of_original, used_c_names = env in
  Hashtbl.copy c_of_original, Hashtbl.copy used_c_names

let mapping = fst

let skip_prefix lid =
  List.exists (fun p -> Bundle.pattern_matches_lid p lid) !Options.no_prefix

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
  List.exists (fun p -> Bundle.pattern_matches_lid p lid) patterns

let rename_prefix lid =
  List.find_map (fun b ->
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
            | T.Up -> Char.uppercase_ascii c
            | T.Low -> Char.lowercase_ascii c
          in
          if Char.uppercase_ascii c = c then
            what_next := T.Low
          else if Char.lowercase_ascii c = c then
            what_next := T.Keep;
          Buffer.add_char b c_next
    done;
    Buffer.contents b
  else
    String.uppercase_ascii (String.sub name 0 1) ^
    String.sub name 1 (String.length name - 1)

let camel_case name =
  let name = pascal_case name in
  String.lowercase_ascii (String.sub name 0 1) ^
  String.sub name 1 (String.length name - 1)

let strip_leading_underscores name =
  let i = ref 0 in
  while name.[!i] = '_' do incr i done;
  if !i = String.length name then
    failwith "cannot have a name made of a single underscore";
  String.sub name !i (String.length name - !i)

type kind = Macro | Type | Other

(* Clients feed the result of this to extend -- this is a tentative name that
   may still generate a collision. *)
let target_c_name ~attempt_shortening ?(kind=Other) lid =
  (* A non-modular renaming is one that is influenced by command-line
     options (e.g. -no-prefix, -bundle ...[rename-prefix], etc.). Such name
     choices pose difficulties in the verified library + verified client
     scenario, because the client needs to replicate the same options in order
     to be able to link against the library. *)
  let pre_name, non_modular_renaming =
    if skip_prefix lid && not (ineligible lid) then
      snd lid, true
    else if attempt_shortening && !Options.short_names && not (ineligible lid) && snd lid <> "main" then
      snd lid, false
    else match rename_prefix lid with
    | Some prefix ->
        prefix ^ "_" ^ snd lid, true
    | None ->
        string_of_lident lid, false
  in
  let formatted_name =
    if !Options.microsoft then
      if pre_name = "main" then
        pre_name
      else
        match kind with
        | Other ->
            pascal_case pre_name
        | Macro ->
            strip_leading_underscores pre_name
        | Type ->
            String.uppercase_ascii (strip_leading_underscores pre_name)
    else
      pre_name
  in
  let formatted_name = if kind = Macro then String.uppercase_ascii formatted_name else formatted_name in
  formatted_name, non_modular_renaming

let to_c_name ?kind m lid =
  try
    fst (Hashtbl.find m lid)
  with Not_found ->
    (* Note: this happens for external types which are not retained as DType
       nodes and therefore are not recorded in the initial name-assignment
       phase. *)
    Idents.to_c_identifier (fst (target_c_name ?kind ~attempt_shortening:false lid))

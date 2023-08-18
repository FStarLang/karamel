(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 License. *)

(** The type of a single bundle -- this avoids a cyclic dependency between
 * [Parser] and [Bundles] *)

(** Crypto.Chacha20=Crypto.Symmetric.Chacha20.*,Crypto.Flag *)

type t = api list * pat list * attr list

and api = string list

and attr = Rename of string | RenamePrefix

and pat =
  | Module of string list
  | Prefix of string list

(* Pretty-printing functions. *)
let string_of_mident mident =
  String.concat "." mident

let string_of_api = string_of_mident

let string_of_apis apis =
  String.concat "+" (List.map string_of_api apis)

let string_of_pattern = function
  | Module m -> String.concat "." m
  | Prefix p -> String.concat "." (p @ [ "*" ])

let string_of_patterns patterns =
  String.concat "," (List.map string_of_pattern patterns)

let string_of_attr = function
  | Rename s -> "rename=" ^ s
  | RenamePrefix -> "rename-prefix"

let string_of_attrs attrs =
  String.concat "," (List.map string_of_attr attrs)

let string_of_bundle (apis, patterns, attrs) =
  let string_of_apis = function [] -> "" | apis -> string_of_apis apis ^ "=" in
  let string_of_attrs = function [] -> "" | attrs -> "[" ^ string_of_attrs attrs ^ "]" in
  string_of_apis apis ^ string_of_patterns patterns ^ string_of_attrs attrs

module LidMap = Idents.LidMap

(* Create a map from an lid to the file it now appears in (after bundling). *)
let mk_file_of files =
  let file_of = List.fold_left (fun map (name, decls) ->
    List.fold_left (fun map decl ->
      LidMap.add (Ast.lid_of_decl decl) name map
    ) map decls
  ) LidMap.empty files in
  let file_of lid =
    try
      Some (LidMap.find lid file_of)
    with Not_found ->
      None
  in
  file_of

(** A given pattern matches an F* filename (i.e. a string using the underscore
 * as a separator *)
let pattern_matches (p: pat) (m: string) =
  match p with
  | Module m' ->
      String.concat "_" m' = m
  | Prefix p ->
      p = [] || KString.starts_with m (String.concat "_" p ^ "_")

(* For generating the filename. NOT for pretty-printing. *)
let bundle_filename (api, patterns, attrs) =
  match KList.find_opt (function Rename s -> Some s | _ -> None) attrs with
  | Some s ->
      s
  | _ ->
      match api with
      | [] ->
          String.concat "_" (KList.map_flatten (function
            | Module m -> m
            | Prefix p -> p
          ) patterns)
      | _ ->
         String.concat "_" (List.map (String.concat "_") api)

let attrs_of_bundle (_, _, attrs) =
  attrs

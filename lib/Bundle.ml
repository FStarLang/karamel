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
  | Lid of (string list * string)

(* Pretty-printing functions. *)
let string_of_mident mident =
  String.concat "." mident

let string_of_api = string_of_mident

let string_of_apis apis =
  String.concat "+" (List.map string_of_api apis)

let string_of_pattern = function
  | Module m -> String.concat "." m
  | Prefix p -> String.concat "." (p @ [ "*" ])
  | Lid (m, n) -> String.concat "." m ^ "." ^ n

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

let rec prefix_of p1 p2 =
  match p1, p2 with
  | [], _ -> true
  | hd1 :: p1, hd2 :: p2 -> hd1 = hd2 && prefix_of p1 p2
  | _ -> false

let pattern_matches_lid (p: pat) (l: string list * string) =
  match p with
  | Module m' ->
      m' = fst l
  | Prefix p ->
      prefix_of p (fst l)
  | Lid l' ->
      l = l'

let pattern_matches_file (p: pat) (name: string) =
  match p with
  | Lid _ -> false
  | Module ns -> name = String.concat "_" ns
  | Prefix ns -> KString.starts_with name (String.concat "_" ns ^ "_")

(** A given pattern matches an F* filename (i.e. a string using the underscore
 * as a separator *)

(* For generating the filename. NOT for pretty-printing. *)
let bundle_filename (api, patterns, attrs) =
  match List.find_map (function Rename s -> Some s | _ -> None) attrs with
  | Some s ->
      s
  | _ ->
      match api with
      | [] ->
          String.concat "_" (List.concat_map (function
            | Module m -> m
            | Prefix p -> p
            | Lid _ -> failwith "impossible"
          ) patterns)
      | _ ->
         String.concat "_" (List.map (String.concat "_") api)

let attrs_of_bundle (_, _, attrs) =
  attrs

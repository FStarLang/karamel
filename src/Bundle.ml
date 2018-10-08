(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 License. *)

(** The type of a single bundle -- this avoids a cyclic dependency between
 * [Parser] and [Bundles] *)

(** Crypto.Chacha20=Crypto.Symmetric.Chacha20.*,Crypto.Flag *)

type t = api list * pat list

and api = mident * visibility

and mident = string list

and visibility = Public | AsIs

and pat =
  | Module of string list
  | Prefix of string list

(* Pretty-printing functions. *)
let string_of_mident mident =
  String.concat "." mident

let string_of_api (mident, visibility) =
  match visibility with
  | AsIs -> string_of_mident mident
  | Public -> "public(" ^ string_of_mident mident ^ ")"

let string_of_apis apis =
  String.concat "+" (List.map string_of_api apis)

let string_of_pattern = function
  | Module m -> String.concat "." m
  | Prefix p -> String.concat "." (p @ [ "*" ])

let string_of_patterns patterns =
  String.concat "," (List.map string_of_pattern patterns)

let string_of_bundle (apis, patterns) =
  match apis with
  | [] ->
      string_of_patterns patterns
  | _ ->
      string_of_apis apis ^ "=" ^
      string_of_patterns patterns

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

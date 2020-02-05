(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 License. *)

type t

type mapping = (Ast.lident, Ast.ident) Hashtbl.t

(** Allocate a new (mutable) table for a given C scope of top-level declarations. *)
val create: unit -> t

(** `extend t name c_name` tries to associate `c_name` to `name` in the table
 * `t`. If case there is a name conflict or `c_name` is an invalid C identifier,
 * a suitable replacement name based on `c_name` will be chosen. *)
val extend: t -> t -> bool -> Ast.lident -> string -> string

(** `lookup t name fallback` recalls the C name associated to `name` in `t`. *)
val lookup: t -> Ast.lident -> string option

val mapping: t -> mapping

val dump: t -> unit

val clone: t -> t

val target_c_name: attempt_shortening:bool -> is_macro:bool -> Ast.lident -> string

val to_c_name: mapping -> Ast.lident -> string

val pascal_case: string -> string
val camel_case: string -> string

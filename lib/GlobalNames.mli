(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 and MIT Licenses. *)

type t

type kind = Macro | Type | Other

(* Each name lives in one of three namespaces: macros, types, or other identifiers. Any two
   namespaces conflict with one another, except for types and other identifiers. *)
type mapping = (Ast.lident * kind, Ast.ident * bool) Hashtbl.t

(** Allocate a new (mutable) table for a given C scope of top-level declarations. *)
val create: unit -> t

(** Given:
  - a global mapping, meaning names that are externally-visible (to a given krml run)
  - a local mapping, for names that are local to this file only,
  - a flag that indicates whether the name is local
  - a source name in a particular namespace
  - the result of a call to `target_c_name`
  the `extend` function returns a C name that is guaranteed to not cause conflicts, and modifies the
  global and local mappings accordingly. *)
val extend: t -> t -> bool -> Ast.lident * kind -> (string * bool) -> string

(** `lookup t name fallback` recalls the name associated to `name` in `t`, or returns `None`; unlike
    `to_c_name`, should the name not be in the map, the function does not make a default choice *)
val lookup: t -> Ast.lident * kind -> string option

val mapping: t -> mapping

val dump: t -> unit

val clone: t -> t

val target_c_name: attempt_shortening:bool -> ?kind:kind -> Ast.lident -> string * bool

(* Lookup a name, providing a built-in, deterministic, C-compatible fallback name for `lident`s that
   are not mapped. *)
val to_c_name: mapping -> Ast.lident * kind -> string

val pascal_case: string -> string
val camel_case: string -> string

val skip_prefix: Ast.lident -> bool

val keywords: string list

val rename_prefix: Ast.lident -> string option

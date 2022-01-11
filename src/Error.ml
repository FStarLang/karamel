(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 License. *)

open Ast

type t = location * raw_error

and raw_error =
  | Dropping of string * t
  | UnboundReference of string
  | BadFrame of string
  | TypeError of string
  | Unsupported of string
  | ExternalError of string
  | ExternalTypeApp of lident
  | Vla of ident
  | LostStatic of string option * lident * string option * lident (* UNUSED *)
  | LostInline of string option * lident * string option * lident
  | MustCallKrmlInit
  | Deprecated of string * string
  | NotLowStar of expr
  | NeedsCompat of lident * string
  | NotWasmCompatible of lident * string
  | DropDeclaration of lident * string
  | NotTailCall of lident
  | GeneratesLetBindings of string * expr * (binder * expr) list
  | Arity of lident * string
  | NotInitializerConstant of lident * expr
  | BundleCollision of string
  | IfDef of lident
  | CannotMacro of lident
  | DropCtypesDeclaration of lident * lident
  | ConflictMacro of lident * string

and location =
  string

let compare = compare

(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 and MIT Licenses. *)

(* This file defines the constants used in the input AST.
   This is separate from Constant.ml to decouple the two. In particular,
   the InputAst includes a "Bool" width that is not present in
   the internal Ast. Removing them from the InputAst is an ABI-breaking
   change that can be done at a later point. *)

type width =
  | UInt8 | UInt16 | UInt32 | UInt64 | Int8 | Int16 | Int32 | Int64
  | Bool
  | CInt (** Checked signed integers. *)
  | SizeT | PtrdiffT
  | Float32 | Float64 (** Floating point numbers. *)
  | Float16
  [@@deriving yojson,show]

type t = width * string
  [@@deriving yojson,show]

type op =
  (* Arithmetic operations *)
  | Add | AddW | Sub | SubW | Div | DivW | Mult | MultW | Mod
  (* Bitwise operations *)
  | BOr | BAnd | BXor | BShiftL | BShiftR | BNot
  (* Arithmetic comparisons / boolean comparisons *)
  | Eq | Neq | Lt | Lte | Gt | Gte
  (* Boolean operations *)
  | And | Or | Xor | Not
  (* Effectful operations. Only appears in C. *)
  | Assign | PreIncr | PreDecr | PostIncr | PostDecr
  (* Misc *)
  | Comma
  | Neg
  [@@deriving yojson,show]

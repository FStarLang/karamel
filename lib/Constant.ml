(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 and MIT Licenses. *)

(** Machine integers. Don't repeat the same thing everywhere. *)

type t = width * string
  [@@deriving yojson, show]

and width =
  | UInt8 | UInt16 | UInt32 | UInt64 | Int8 | Int16 | Int32 | Int64
  | Bool
  | CInt (** Checked signed integers. *)
  | SizeT | PtrdiffT
  | Float32 | Float64 (** Floating point numbers. *)

let bytes_of_width (w: width) =
  match w with
  | UInt8 -> 1
  | UInt16 -> 2
  | UInt32 -> 4
  | UInt64 -> 8
  | Int8 -> 1
  | Int16 -> 2
  | Int32 -> 4
  | Int64 -> 8
  | CInt -> 4
  | _ -> invalid_arg "bytes_of_width"

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

(* Determines is this is a comparison operator *)
let is_comp_op = function
  | Eq | Neq | Lt | Lte | Gt | Gte -> true
  | _ -> false

let is_float = function
  | Float32 | Float64 -> true
  | _ -> false

(* Negates the comparison operator *)
let comp_neg = function
  | Eq -> Neq
  | Neq -> Eq
  | Lt -> Gte
  | Lte -> Gt
  | Gt -> Lte
  | Gte -> Lt
  | _ -> failwith "not a comparison operator"

let unsigned_of_signed = function
  | Int8 -> UInt8
  | Int16 -> UInt16
  | Int32 -> UInt32
  | Int64 -> UInt64
  | CInt | UInt8 | UInt16 | UInt32 | UInt64 | SizeT | PtrdiffT | Bool
  | Float32 | Float64 -> raise (Invalid_argument "unsigned_of_signed")

let is_signed = function
  | Int8 | Int16 | Int32 | Int64 | CInt | PtrdiffT -> true
  | UInt8 | UInt16 | UInt32 | UInt64 | SizeT -> false
  | Bool | Float32 | Float64 -> raise (Invalid_argument "is_signed")

let is_unsigned w = not (is_signed w)

let without_wrap = function
  | AddW -> Add
  | SubW -> Sub
  | MultW -> Mult
  | DivW -> Div
  | _ -> raise (Invalid_argument "without_wrap")

let uint8_of_int i =
  assert (i < (1 lsl 8) && i >= 0);
  UInt8, string_of_int i

let uint32_of_int i =
  assert (i < (1 lsl 32) && i >= 0);
  UInt32, string_of_int i

(* New: polymorphic equalities, treated properly, finally (Feb 2021)
   Some background info... initially, equalities were only accepted by KaRaMeL
   at base scalar types (int, bool) that have a "width". However, with time
   passing, KaRaMeL gained the ability to monomorphize functions and therefore
   had to accept equalities on data types, units, and so on. Equalities on base
   types were represented as `Op (Eq, w)` while equalities on complex types were
   represented as `TApp (Op (Eq, <dummy width>), t)` which was clearly
   suboptimal.

   Now, any occurrence of equality is represented as EPolyComp (Eq, t) where t
   can be any type. This allows removing the kludge of dummy values, and also
   allows keeping equalities on types without a width (e.g. an enum) that we
   nonetheless know will be comparable with a target Eq operator.

   For that reason, we keep Eq and Neq in the op type above, even though they
   will with this patch only be used for pretty-printing (like, the comma
   operator). *)
type poly_comp = PEq | PNeq

let op_of_poly_comp = function PEq -> Eq | PNeq -> Neq

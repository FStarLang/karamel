(** Machine integers. Don't repeat the same thing everywhere. *)

type t = width * string

and width =
  | UInt8 | UInt16 | UInt32 | UInt64 | Int8 | Int16 | Int32 | Int64

type op =
  | Add | AddW | Sub | SubW | Div | Mult | Mod
  | BOr | BAnd | BXor | BShiftL | BShiftR
  | Eq | Lt | Lte | Gt | Gte

let unsigned_of_signed = function
  | Int8 -> UInt8
  | Int16 -> UInt16
  | Int32 -> UInt32
  | Int64 -> UInt64
  | UInt8 | UInt16 | UInt32 | UInt64 -> raise (Invalid_argument "unsigned_of_signed")

let is_signed = function
  | Int8 | Int16 | Int32 | Int64 -> true
  | UInt8 | UInt16 | UInt32 | UInt64 -> false

let is_unsigned w = not (is_signed w)

let without_wrap = function
  | AddW -> Add
  | SubW -> Sub
  | _ -> raise (Invalid_argument "without_wrap")

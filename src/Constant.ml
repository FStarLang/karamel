(** Machine integers. Don't repeat the same thing everywhere. *)

type t = width * string

and width =
  UInt8 | UInt16 | UInt32 | UInt64 | Int8 | Int16 | Int32 | Int64

type op = Add | AddW | Sub | Div | Mult | Mod | Or | And | Xor | ShiftL | ShiftR

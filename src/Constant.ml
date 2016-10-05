(** Machine integers. Don't repeat the same thing everywhere. *)

type t = width * string
  [@@deriving yojson]

and width =
  | UInt8 | UInt16 | UInt32 | UInt64 | Int8 | Int16 | Int32 | Int64
  | Bool
  | Int | UInt
    (** For internal use only *)

type op =
  (* Arithmetic operations *)
  | Add | AddW | Sub | SubW | Div | DivW | Mult | MultW | Mod
  (* Bitwise operations *)
  | BOr | BAnd | BXor | BShiftL | BShiftR | BNot
  (* Arithmetic comparisons / boolean comparisons *)
  | Eq | Neq | Lt | Lte | Gt | Gte
  (* Boolean operations *)
  | And | Or | Xor | Not
  (* Effectful operations *)
  | Assign | PreIncr | PreDecr | PostIncr | PostDecr
  (* Misc *)
  | Comma
  [@@deriving yojson]

let unsigned_of_signed = function
  | Int8 -> UInt8
  | Int16 -> UInt16
  | Int32 -> UInt32
  | Int64 -> UInt64
  | Int -> UInt
  | UInt | UInt8 | UInt16 | UInt32 | UInt64 | Bool -> raise (Invalid_argument "unsigned_of_signed")

let is_signed = function
  | Int8 | Int16 | Int32 | Int64 | Int -> true
  | UInt8 | UInt16 | UInt32 | UInt64 | UInt -> false
  | Bool -> raise (Invalid_argument "is_signed")

let is_unsigned w = not (is_signed w)

let without_wrap = function
  | AddW -> Add
  | SubW -> Sub
  | MultW -> Mult
  | DivW -> Div
  | _ -> raise (Invalid_argument "without_wrap")

let of_int i =
  assert (i < 256 && i >= 0);
  UInt8, string_of_int i

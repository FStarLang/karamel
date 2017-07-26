(** CFlat, without structures and with computed stack frames. *)

(** The point of this IR is to:
  * - compute the size of the stack frames;
  * - remove structs and enums, favoring instead n-ary parameters and variables,
  *   along with constant numbers for enums.
  * We keep the size of machine operations, so that we know which sequence of
  * instructions to emit (e.g. for small int types, we want to add a
  * truncation); we also keep the signedness to pick the right operator.
  *)
open Common

module K = Constant

module Sizes = struct

  (** There are only two sizes for values in Wasm. A Low* 64-bit integer maps to
   * I64; everything else maps to I32. *)
  type size =
    | I32
    | I64
    [@@deriving show]

  (* We may want, however, to adopt a more optimal representation for arrays, and
   * store bytes within arrays. Therefore, there is a different notion of how
   * arrays are indexed. *)
  and array_size =
    | A8
    | A16
    | A32
    | A64

  let string_of_size = function
    | I32 -> "I32"
    | I64 -> "I64"

  let string_of_array_size = function
    | A8 -> "8"
    | A16 -> "16"
    | A32 -> "32"
    | A64 -> "64"

  let size_of_width (w: K.width) =
    let open K in
    match w with
    | UInt64 | Int64 | UInt | Int ->
        I64
    | _ ->
        I32

  let array_size_of_width (w: K.width) =
    let open K in
    match w with
    | UInt64 | Int64 | UInt | Int ->
        A64
    | UInt32 | Int32 ->
        A32
    | UInt16 | Int16 ->
        A16
    | UInt8 | Int8 ->
        A8
    | Bool ->
        invalid_arg "array_size_of_width"

  let bytes_in = function
    | A8 -> 1
    | A16 -> 2
    | A32 -> 4
    | A64 -> 8
end

open Sizes

type program =
  decl list

and decl =
  | Global of ident * size * expr * bool
  | Function of function_t
  | External of ident * size list (* args *) * size list (* ret *)

and function_t = {
  name: ident;
  args: size list;
  ret: size list;
  locals: locals;
  body: expr;
  public: bool;
}

(* This is NOT De Bruijn *)
and locals =
  size list

and expr =
  | Var of var
  | GetGlobal of ident
  | Constant of K.width * string
  | Assign of var * expr
  | StringLiteral of string
  | Abort

  | IfThenElse of expr * expr * expr * size
  | While of expr * expr
  | Switch of expr * (expr * expr) list
  | Sequence of expr list
  | Ignore of expr * size

  | BufCreate of lifetime * expr * array_size
  | BufRead of expr * expr * array_size
  | BufSub of expr * expr * array_size
  | BufWrite of expr * expr * expr * array_size

  | PushFrame
  | PopFrame

  | CallOp of op * expr list
  | CallFunc of ident * expr list
  | Cast of expr * K.width * K.width
      (** from; to *)
  [@@deriving show]

and var =
  int (** NOT De Bruijn *)

and op = K.width * K.op

and ident =
  string

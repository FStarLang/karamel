(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 License. *)

(** CFlat, without structures and with computed stack frames. *)

(** The point of this IR is to:
  * - compute the size of the stack frames;
  * - remove structs and enums, favoring instead n-ary parameters and variables,
  *   along with constant numbers for enums.
  * We keep the size of machine operations, so that we know which sequence of
  * instructions to emit (e.g. for small int types, we want to add a
  * truncation); we also keep the signedness to pick the right operator.
  *)
module K = Constant

module Sizes = struct

  (** There are only two sizes for values in Wasm. A Low* 64-bit integer maps to
   * I64; everything else maps to I32. *)
  type size =
    | I32
    | I64
    [@@deriving show, yojson]

  (* We may want, however, to adopt a more optimal representation for arrays, and
   * store bytes within arrays. Therefore, there is a different notion of how
   * arrays are indexed. *)
  and array_size =
    | A8
    | A16
    | A32
    | A64

  (** For the JS boundary functions *)
  and runtime_type =
    | Int of array_size
    | Pointer of runtime_type
    | Layout of string
    | Union of runtime_type list
    | Unknown (* anonymous struct / unions *)

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
    | UInt64 | Int64 ->
        I64
    | _ ->
        I32

  let array_size_of_width (w: K.width) =
    let open K in
    match w with
    | UInt64 | Int64 | CInt ->
        A64
    | UInt32 | Int32 ->
        A32
    | UInt16 | Int16 ->
        A16
    | UInt8 | Int8 ->
        A8
    | Bool | SizeT | PtrdiffT ->
        invalid_arg "array_size_of_width"

  let bytes_in = function
    | A8 -> 1
    | A16 -> 2
    | A32 -> 4
    | A64 -> 8
end

type program =
  decl list

and decl =
  | Global of ident * size * expr * expr list * bool
  | Function of function_t
  | ExternalFunction of ident * size list (* args *) * size list (* ret *)
  | ExternalGlobal of ident * size
  [@@deriving show,
    visitors { variety = "iter" }]

and size = Sizes.size [@opaque]
and array_size = Sizes.array_size [@opaque]
and width = K.width [@opaque]
and op = K.op [@opaque]
and lifetime = Common.lifetime [@opaque]

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

and constant =
  width * string

and expr =
  | Var of var
  | GetGlobal of ident
  | Constant of constant
  | Assign of var * expr
  | StringLiteral of string
  | Abort of expr

  | IfThenElse of expr * expr * expr * size
  | While of expr * expr
  | Switch of expr * (constant * expr) list * expr option (* default case *) * size
  | Sequence of expr list
  | Ignore of expr * size

  | BufCreate of lifetime * expr * array_size
  | BufSub of expr * expr * array_size
  | BufRead of expr * int * array_size
      (** Constant offset expressed in number of BYTES. *)
  | BufWrite of expr * int * expr * array_size
      (** Ibid. *)

  | CallOp of op_ * expr list
  | CallFunc of ident * expr list
  | Cast of expr * width * width
      (** from; to *)
  | CastI64ToPacked of expr

and var =
  int (** NOT De Bruijn *)

and op_ = width * op

and ident =
  string

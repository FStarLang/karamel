(** CFlat, without structures and with computed stack frames. *)

(** The point of this IR is to:
  * - compute the size of the stack frames;
  * - remove structs and enums, favoring instead n-ary parameters and variables,
  *   along with constant numbers for enums.
  * We keep the size of machine operations, so that we know which sequence of
  * instructions to emit (e.g. for small int types, we want to add a
  * truncation); we also the signedness to pick the right operator.
  *)
open Common

module K = Constant

type program =
  decl list

and decl =
  | Global of ident * size * expr
  | Function of function_t
  | External of ident * size list (* args *) * size list (* ret *)

and function_t = {
  name: ident;
  args: size list;
  ret: size list;
  locals: locals;
  body: stmt list;
  public: bool;
}

(* This is NOT De Bruijn *)
and locals =
  size list

and stmt =
  | Abort
  | Return of expr option
  | Ignore of expr
  | IfThenElse of expr * block * block
  | While of expr * block
  | Assign of (var * size) * expr
  | Copy of expr * size * expr
  | Switch of expr * (ident * block) list
  | BufWrite of expr * expr * expr
  | BufBlit of expr * expr * expr * expr * expr
  | BufFill of expr * expr * expr
  | PushFrame
  | PopFrame

and expr =
  | CallOp of op * expr list
  | CallFunc of ident * expr list
  | Var of var * size
  | Qualified of ident * size
    (** Loading from a local or global slot requires knowing which size the
     * resulting operand should have. For instance, we may end up loading a
     * 32-bit variable from a 64-bit slot, or a byte from a word-sized slot. *)
  | Constant of K.width * string
  | BufCreate of lifetime * expr * expr
  | BufCreateL of lifetime * expr list
  | BufRead of expr * expr
  | BufSub of expr * expr
  | Bool of bool
  | Comma of expr * expr
  | StringLiteral of string
  | Any

and block =
  stmt list

and op = K.width * K.op

and var =
  int

and ident =
  string

and size =
  | I32
  | I64

let size_of_width (w: K.width) =
  let open K in
  match w with
  | UInt64 | Int64 | UInt | Int ->
      I64
  | _ ->
      I32

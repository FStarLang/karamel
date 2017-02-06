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
  | Global of ident * size * expr * bool
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
  | Assign of var * expr
  | Copy of expr * expr * size * expr
    (** Destination, source, element size, number of elements *)
  | Switch of expr * (expr * block) list
  | BufWrite of expr * expr * expr
  | BufBlit of expr * expr * expr * expr * expr
  | BufFill of expr * expr * expr
  | PushFrame
  | PopFrame
  [@@ deriving show]

and expr =
  | CallOp of op * expr list
  | CallFunc of ident * expr list
  | Var of var
  | Qualified of ident
  | Constant of K.width * string
  | BufCreate of lifetime * expr * expr
  | BufCreateL of lifetime * expr list
  | BufRead of expr * expr
  | BufSub of expr * expr
  | Comma of expr * expr
  | StringLiteral of string
  | Cast of expr * K.width * K.width
      (** from; to *)
  | Any

and block =
  stmt list

and var =
  int (** NOT De Bruijn *)

and op = K.width * K.op

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

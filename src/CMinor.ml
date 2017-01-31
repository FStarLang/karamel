(** In CMinor, the size of stack frames has been computed. Structs, enums are
 * gone. The only two sizees left are I32 and I64. *)

open Common

module K = Constant

type program =
  decl list

and decl =
  | Global of ident * size * expr
  | Function of function_t
  | External of ident * size

and function_t = {
  name: ident;
  args: size list;
  ret: size list;
  locals: locals;
  body: stmt list;
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
  | Assign of expr * expr
  | Copy of expr * size * expr
  | Switch of expr * (ident * block) list
      (** The ident is one of the constants *)
  | BufWrite of expr * expr * expr
  | BufBlit of expr * expr * expr * expr * expr
  | BufFill of expr * expr * expr
  | PushFrame
  | PopFrame

and expr =
  | Call of expr * expr list
  | Var of var
  | Qualified of ident
    (** A global, or an enum constant. *)
  | Constant of K.t
  | BufCreate of lifetime * expr * expr
  | BufCreateL of lifetime * expr list
  | BufRead of expr * expr
  | BufSub of expr * expr
  | Op of op
  | Bool of bool
  | Comma of expr * expr
  | StringLiteral of string
  | Any

and block =
  stmt list

and op = K.op

and var =
  int

and ident =
  string

and size =
  | I32
  | I64

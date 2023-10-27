(* A minimalistic representation of Rust *)

type borrow_kind = Mut | Shared

type typ =
  | Constant of Constant.width (* excludes cint, ptrdifft *)
  | Ref of borrow_kind * typ
  | Array of typ * int
  | Slice of typ (* always appears underneath Ref *)
  | Unit
  | Function of typ list * typ

let bool = Constant Bool
let u32 = Constant UInt32
let usize = Constant SizeT

(* Some design choices.
   - We don't intend to perform any deep semantic transformations on this Rust
     representation, but just in case, we retain DeBruijn indices.
   - Rust is an expression-based language, so we don't enforce a distinction
     between statements and expressions -- Rust is not as strict as C in that
     regard. We'll do "the right thing" once we go to a concrete Rust syntax
     tree prior to pretty-printing. *)
type db_index = int

type binding = string * typ

(* Top-level declarations *)
type name = string list

type array_expr =
  | List of expr list
  | Repeat of expr * expr (* [ e; n ] *)

and expr =
  | Operator of Constant.op
  | Array of array_expr
  | Name of name
  | Var of db_index
  | Ref of borrow_kind * expr
  | Index of expr * expr
  | Constant of Constant.t
  | Let of binding * expr
  | Call of expr * expr list
    (** Note that this representation admits empty argument lists -- Ast always
        takes unit *)
  | Unit
  | Panic of string
  | IfThenElse of expr * expr * expr option
  | Assign of expr * expr

type decl =
  | Function of binding list * typ * expr

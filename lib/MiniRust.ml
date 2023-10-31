(* A minimalistic representation of Rust *)

type borrow_kind = Mut | Shared

type typ =
  | Constant of Constant.width (* excludes cint, ptrdifft *)
  | Ref of borrow_kind * typ
  | Vec of typ
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
  | VecNew of array_expr
  | Name of name
  | Borrow of borrow_kind * expr
  | Constant of Constant.t
  | Let of binding * expr * expr
  | Call of expr * expr list
    (** Note that this representation admits empty argument lists -- as opposed
        to Ast which always takes unit *)
  | Unit
  | Panic of string
  | IfThenElse of expr * expr * expr option
  | Assign of place * expr
  | As of expr * typ
  | Place of place
      (** Injection of lvalues ("places") into rvalues ("expressions") *)
  | For of binding * expr
  | While of expr * expr

and place =
  | Var of db_index
  | Index of place * expr

type decl =
  | Function of {
    name: name;
    parameters: binding list;
    return_type: typ;
    body: expr
  }

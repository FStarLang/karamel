(** Definition of C* *)

module K = Constant

type program =
  decl list

and decl =
  | Global of ident * typ * expr
  | Function of typ * ident * binder list * block
  | Type of ident * typ
  | External of ident * typ

and stmt =
  | Return of expr option
  | Ignore of expr
  | Decl of binder * expr
    (** Scope is: statements that follow. *)
  | IfThenElse of expr * block * block
  | While of expr * block
  | Assign of expr * expr
    (** First expression has to be a [Bound] or [Open]. *)
  | BufWrite of expr * expr * expr
    (** First expression has to be a [Bound] or [Open]. *)
  | BufBlit of expr * expr * expr * expr * expr
  | PushFrame
  | PopFrame
  | Abort

and expr =
  | Call of expr * expr list
    (** First expression has to be a [Qualified] or an [Op]. *)
  | Var of ident
  | Qualified of lident
  | Constant of K.t
  | BufCreate of expr * expr
  | BufCreateL of expr list
  | BufRead of expr * expr
  | BufSub of expr * expr
  | Op of op
  | Cast of expr * typ
  | Bool of bool
  | Struct of ident * (ident option * expr) list
    (** Either all names are provided, or no names are provided *)
  | Field of expr * ident
  | Comma of expr * expr
  | Any

and block =
  stmt list

and op = K.op

and var =
  int

and binder = {
  name: ident;
  typ: typ;
}

and ident =
  string

and lident =
  ident list * ident

and typ =
  | Int of Constant.width
  | Pointer of typ
  | Void
  | Qualified of lident
  | Array of typ * expr
  | Function of typ * typ list
      (** Return type, arguments *)
  | Bool
  | Z
  | Struct of ident option * (ident * typ) list
  | Enum of ident option * ident list

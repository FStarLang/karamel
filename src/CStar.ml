(** Definition of C* *)

module K = Constant

type program =
  decl list

and decl =
  | Function of typ * ident * binder list * block
  | TypeAlias of ident * typ
  | Global of ident * typ * expr

and stmt =
  | Return of expr
  | Ignore of expr
  | Decl of binder * expr
    (** Scope is: statements that follow. *)
  | IfThenElse of expr * block * block
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
  | BufRead of expr * expr
  | BufSub of expr * expr
  | Op of op
  | Cast of expr * typ
  | Bool of bool
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
  | Bool
  | Z

(** Definition of C* *)

type program =
  decl list

and decl =
  | Function of (typ * ident * binder list * block)
  | TypeAlias of (ident * typ)

and stmt =
  | Call of (expr * expr list)
  | Decl of (binder * expr * expr)
  | IfThenElse of (expr * expr * expr)
  | Assign of (expr * expr)
  | BufWrite of (expr * expr * expr)

and expr =
  | Bound of var
  | Open of binder
  | Qualified of lident
  | Constant of C.t
  | BufCreate of (expr * expr)
  | BufRead of (expr * expr)
  | BufSub of (expr * expr * expr)
  | Op of op

and block =
  stmt list

and op = C.op

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
  | TInt of Constant.width
  | TBuf of typ
  | TVoid
  | TAlias of ident

(** Definition of C* *)

open Common

module K = Constant

type program =
  decl list

and decl =
  | Global of ident * flag list * typ * expr
  | Function of calling_convention option * flag list * typ * ident * binder list * block
  | Type of ident * typ
  | External of ident * typ

and stmt =
  | Abort of string
  | Return of expr option
  | Ignore of expr
  | Decl of binder * expr
    (** Scope is: statements that follow. *)
  | IfThenElse of expr * block * block
  | While of expr * block
  | For of binder * expr * expr * stmt * block
    (** There is a slight mismatch; C has an iteration *expression* but C*'s
     * expressions are pure; therefore, we must use a statement in lieu of the
     * iteration expression. *)
  | Assign of expr * expr
    (** Destination (i.e. Var), Source *)
  | Copy of expr * typ * expr
    (** Destination, always Array (typ, size), Source *)
  | Switch of expr * (ident * block) list
  | BufWrite of expr * expr * expr
    (** First expression has to be a [Bound] or [Open]. *)
  | BufBlit of expr * expr * expr * expr * expr
  | BufFill of expr * expr * expr
  | PushFrame
  | PopFrame
  | Comment of string
  | Block of block

and expr =
  | InlineComment of string * expr * string
  | Call of expr * expr list
    (** First expression has to be a [Qualified] or an [Op]. *)
  | Var of ident
  | Qualified of ident
  | Constant of K.t
  | BufCreate of lifetime * expr * expr
    (** initial value, length *)
  | BufCreateL of lifetime * expr list
  | BufRead of expr * expr
  | BufSub of expr * expr
  | Op of op
  | Cast of expr * typ
    (** to *)
  | Bool of bool
  | Struct of ident option * (ident option * expr) list
    (** Some invariants. A struct can appear in an expression (and comes with
     * the name of the corresponding type definition), or within a struct (will
     * be translated as an initializer list) and may not have a type annotation
     * if the field of the corresponding type definition is anonymous. The
     * expressions are annotated with an (optional) field name. Either all are
     * annotated, or none. *)
  | Field of expr * ident
  | Comma of expr * expr
  | StringLiteral of string
  | Any
  | AddrOf of expr
  | EAbort of typ * string
  [@@deriving show]

and block =
  stmt list

and op = K.op * K.width

and var =
  int

and binder = {
  name: ident;
  typ: typ;
}

and ident =
  string

(** About data types (struct, enum, union):
  * - they never carry a name (we never emit "struct foo { ... }");
  * - they can appear in the body of type definitions, or
  * - as "structural" types that carry no particular name *)
and typ =
  | Int of Constant.width
  | Pointer of typ
  | Void
  | Qualified of ident
  | Array of typ * expr
  | Function of calling_convention option * typ * typ list
      (** Return type, arguments *)
  | Bool
  | Z

  | Struct of (ident option * typ) list
      (** In support of anonymous unions. *)
  | Enum of ident list
  | Union of (ident * typ) list

let ident_of_decl (d: decl): string =
  match d with
  | Global (id, _, _, _)
  | Function (_, _, _, id, _, _)
  | Type (id, _)
  | External (id, _) ->
      id

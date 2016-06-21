(** A (simplified) grammar of C. *)

module K = Constant

(* This pretty-printer based on: http:/ /en.cppreference.com/w/c/language/declarations 
 * Many cases are omitted from this bare-bones C grammar; hopefully, to be extended. *)
type type_spec =
  | Int of Constant.width
  | Void
  | Named of ident

and storage_spec =
  | Typedef

and declarator_and_init =
  declarator * init option

and declarator_and_inits =
  declarator_and_init list

and declarator =
  | Ident of ident
  | Pointer of declarator
  | Array of declarator * K.t
  | Function of declarator * params

and expr =
  | Op1 of K.op * expr
  | Op2 of K.op * expr * expr
  | Index of expr * expr
  | Deref of expr * expr
  | Address of expr * expr
  | Member of expr * expr
  | MemberP of expr * expr
  | Assign of expr * expr
    (** not covering *=, +=, etc. *)
  | Call of expr * expr list
  | Name of ident
  | Cast of expr * type_name
  | Constant of K.t

(** this is a WILD approximation of the notion of "type name" in C _and_ a hack
 * because there's the invariant that the ident found at the bottom of the
 * [declarator] is irrelevant... *)
and type_name =
  type_spec * declarator

and params =
  (* No support for old syntax, e.g. K&R, or [void f(void)]. *)
  param list

and param =
  (** Also approximate. *)
  type_spec * declarator

and declaration =
  type_spec * storage_spec option * declarator_and_inits

and ident =
  string

and init =
  | Expr of expr
  | Initializer of init list

(** Note: according to http:/ /en.cppreference.com/w/c/language/statements,
 * declarations can only be part of a compound statement... we do not enforce
 * this invariant via the type [stmt], but rather check it at runtime (see
 * [mk_compound_if]), as the risk of messing things up, naturally. *)
type stmt =
  | Compound of stmt list
  | Expr of expr
  | SelectIf of expr * stmt
  | SelectIfElse of expr * stmt * stmt
  | Return of expr option
  | Decl of declaration

and program =
  declaration_or_function list

and declaration_or_function =
  | Decl of declaration
  | Function of declaration * stmt
    (** [stmt] _must_ be a compound statement *)

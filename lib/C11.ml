(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 and MIT Licenses. *)

module K = Constant
open Common

(* This pretty-printer based on: http:/ /en.cppreference.com/w/c/language/declarations
 * Many cases are omitted from this bare-bones C grammar; hopefully, to be extended. *)
type type_spec =
  | Int of Constant.width
  | Void
  | Named of ident
  | Struct of ident option * declaration list option
      (** Note: the option allows for zero-sized structs (GCC's C, C++) but as
       * of 2017/05/14 we never generate these. *)
  | Union of ident option * declaration list option
  | Enum of ident option * (ident * Ast.z option) list
    (** not encoding all the invariants here *)
  [@@deriving show]

and storage_spec =
  | Typedef
  | Extern
  | Static

and qualifier =
  | Const
  | Volatile
  | Restrict

and declarator_and_init =
  declarator * alignment option * init option

and alignment =
  expr

and declarator_and_inits =
  declarator_and_init list

and declarator =
  | Ident of ident
  | Pointer of qualifier list * declarator
  | Array of qualifier list * declarator * expr
  | Function of calling_convention option * declarator * params

and expr =
  | Op1 of K.op * expr
  | Op2 of K.op * expr * expr
  | Index of expr * expr
  | Deref of expr
  | Address of expr
  | Member of expr * expr
  | MemberP of expr * expr
  | Assign of expr * expr
    (** not covering *=, +=, etc. *)
  | Call of expr * expr list
  | Name of ident
  | Cast of type_name * expr
  | Literal of string
  | Constant of K.t
  | Bool of bool
  | Sizeof of expr
  | CompoundLiteral of type_name * init list
  | MemberAccess of expr * ident
  | MemberAccessPointer of expr * ident
  (* The three cases below are NOT in the C grammar *)
  | InlineComment of string * expr * string
  | Type of type_name
  | Stmt of stmt list
  (* Not in the C grammar either; encode a C++ initializer list that appears in expression position
     so as to rely on an implicit constructor *)
  | CxxInitializerList of init
    

(** this is a WILD approximation of the notion of "type name" in C _and_ a hack
 * because there's the invariant that the ident found at the bottom of the
 * [declarator] is irrelevant... *)
and type_name =
  qualifier list * type_spec * declarator

and params =
  (* No support for old syntax, e.g. K&R, or [void f(void)]. *)
  param list

and param =
  (** Also approximate. *)
  qualifier list * type_spec * declarator

and inline_stance =
  | Inline
  | NoInline
  | MustInline
  

and extra = {
    maybe_unused: bool;
    target: string option
}
  (* some extra information that doesn't really pertain to the C standard *)

and declaration =
  qualifier list * type_spec * inline_stance option * storage_spec option * extra * declarator_and_inits
  (* the inline stance is for functions only; in addition to the standard C
     "inline" qualifier, we also distinguish a "noinline" version for
     security-sensitive functions that would otherwise undergo upsetting
     compiler optimizations *)

and ident =
  string

and init =
  | InitExpr of expr
  | Designated of designator * init
  | Initializer of init list

and designator =
  | Dot of ident
  | Bracket of int

(** Note: according to http:/ /en.cppreference.com/w/c/language/statements,
 * declarations can only be part of a compound statement... we do not enforce
 * this invariant via the type [stmt], but rather check it at runtime (see
 * [mk_compound_if]), at the risk of messing things up, naturally. *)
and stmt =
  | Compound of stmt list
  | Decl of declaration
  | Expr of expr
  | If of expr * stmt
  | IfElse of expr * stmt * stmt
  | IfDef of expr * stmt list * (expr * stmt list) list * stmt list
      (* n-ary for pretty-printing purposes; adding it in this AST for more
       * control over pretty-printing, etc. *)
  | While of expr * stmt
  | For of declaration_or_expr * expr * expr * stmt
  | Return of expr option
  | Switch of expr * (expr * stmt) list * stmt
    (** the last component is the default statement *)
  | Break
  | Continue
  | Comment of string
    (** note: this is not in the C grammar *)

and program =
  declaration_or_function list

and comment =
  string

and declaration_or_function =
  | Decl of comment list * declaration
  | Function of comment list * declaration * stmt
    (** [stmt] _must_ be a compound statement *)
  | Text of string
  | Macro of comment list * string * expr
    (** passed in from F*, to be printed as-is *)

and declaration_or_expr = [
  | `Decl of declaration
  | `Expr of expr
  | `Skip
]
[@@deriving show]

type header =
  | Public of program
  | Internal of program


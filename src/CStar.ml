(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 License. *)

(** Definition of C* *)

open Common

module K = Constant

type program =
  decl list

and decl =
  | Global of lident * bool * flag list * typ * expr
    (** The boolean indicates whether this variable is intended to be compiled
     * as a macro. *)
  | Function of calling_convention option * flag list * typ * lident * binder list * block
  | Type of lident * typ * flag list
  | TypeForward of lident * flag list
  | External of lident * typ * flag list * string list
    (** String list for pretty-printing the names of the arguments. *)

and stmt =
  | Abort of string
  | Return of expr option
  | Break
  | Ignore of expr
  | Decl of binder * expr
    (** Scope is: statements that follow. *)
  | IfThenElse of bool * expr * block * block
    (** The boolean indicates whether this is intended to be compiled as an
     * ifdef. *)
  | While of expr * block
  | For of [ `Decl of binder * expr | `Stmt of stmt | `Skip ] * expr * stmt * block
    (** There is a slight mismatch; C has an iteration *expression* but C*'s
     * expressions are pure; therefore, we must use a statement in lieu of the
     * iteration expression. *)
  | Assign of expr * typ * expr
    (** Destination (i.e. Var), Source *)
  | Switch of expr * ([`Ident of lident | `Int of K.t] * block) list * block option
  | BufWrite of expr * expr * expr
    (** First expression has to be a [Bound] or [Open]. *)
  | BufBlit of typ * expr * expr * expr * expr * expr
  | BufFill of typ * expr * expr * expr
  | BufFree of expr
  | Block of block
  | Comment of string

and expr =
  | InlineComment of string * expr * string
  | Call of expr * expr list
    (** First expression has to be a [Qualified] or an [Op]. *)
  | Var of ident
  | Qualified of lident
  | Macro of lident
  | Constant of K.t
  | BufCreate of lifetime * expr * expr
    (** initial value, length *)
  | BufCreateL of lifetime * expr list
    (** no need for types on bufcreate; they're either under a (typed) binder or
     * on the rhs of a (typed) assignment *)
  | BufRead of expr * expr
  | BufSub of expr * expr
  | Op of op
  | Cast of expr * typ
    (** to *)
  | Bool of bool
  | Struct of lident option * (ident option * expr) list
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

and lident =
  string list * string

(** About data types (struct, enum, union):
  * - they never carry a name (we never emit "struct foo { ... }");
  * - they can appear in the body of type definitions, or
  * - as "structural" types that carry no particular name *)
and typ =
  | Int of Constant.width
  | Pointer of typ
  | Void
  | Qualified of lident
  | Array of typ * expr
  | Function of calling_convention option * typ * typ list
      (** Return type, arguments *)
  | Bool
  | Struct of (ident option * typ) list
      (** In support of anonymous unions. *)
  | Enum of lident list
  | Union of (ident * typ) list
  | Const of typ
      (* note: when we have restrict, or MinLength, extend this to be a
       * Qualifier node or something more general *)

let lid_of_decl (d: decl): lident =
  match d with
  | Global (id, _, _, _, _)
  | Function (_, _, _, id, _, _)
  | Type (id, _, _)
  | TypeForward (id, _)
  | External (id, _, _, _) ->
      id

let flags_of_decl (d: decl): Common.flag list =
  match d with
  | Global (_, _, flags, _, _)
  | Function (_, flags, _, _, _, _)
  | Type (_, _, flags)
  | TypeForward (_, flags)
  | External (_, _, flags, _) ->
      flags

(* An ad-hoc iterator for the C* equivalent of TQualified *)
let rec iter_typ f: typ -> unit = function
  | Qualified l -> f l
  | Function (_, return_type, parameters) ->
      List.iter (iter_typ f) (return_type :: parameters)
  | Union l ->
      List.iter (fun x -> iter_typ f (snd x)) l
  | Struct l ->
      List.iter (fun x -> iter_typ f (snd x)) l
  | Pointer t
  | Array (t, _)
  | Const t ->
      iter_typ f t
  | Enum _
  | Int _
  | Void
  | Bool ->
      ()

let iter_decl f = function
  | Global (_, _, _, t, _) ->
      iter_typ f t
  | Function (_, _, t, _, bs, _) ->
      iter_typ f t;
      List.iter (fun b -> iter_typ f b.typ) bs
  | Type (_, t, _) ->
      iter_typ f t
  | _ ->
      ()

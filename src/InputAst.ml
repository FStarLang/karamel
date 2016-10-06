(** Definition of the input format. *)

open Utils

module K = Constant

(** The input AST. Note: F* doesn't have flat data constructors, so we need to introduce
 * (inefficient) boxing for the sake of interop. *)

type program =
  decl list
  [@@deriving yojson]

and decl =
  | DGlobal of (flag list * lident * typ * expr)
  | DFunction of (flag list * typ * lident * binder list * expr)
  | DTypeAlias of (lident * int * typ)
      (** Name, number of parameters (De Bruijn), definition. *)
  | DTypeFlat of (lident * (ident * (typ * bool)) list)
      (** The boolean indicates if the field is mutable *)
  | DExternal of (lident * typ)

and flag =
  | Private

and expr =
  | EBound of var
  | EQualified of lident
  | EConstant of K.t
  | EUnit
  | EApp of (expr * expr list)
  | ELet of (binder * expr * expr)
  | EIfThenElse of (expr * expr * expr)
  | ESequence of expr list
  | EAssign of (expr * expr)
    (** left expression can only be a EBound or EOpen *)
  | EBufCreate of (expr * expr)
    (** initial value, length *)
  | EBufRead of (expr * expr)
    (** e1[e2] *)
  | EBufWrite of (expr * expr * expr)
    (** e1[e2] <- e3 *)
  | EBufSub of (expr * expr)
    (** e1 + e2 *)
  | EBufBlit of (expr * expr * expr * expr * expr)
    (** e1, index; e2, index; len *)
  | EMatch of (expr * branches)
  | EOp of (K.op * K.width)
  | ECast of (expr * typ)
  | EPushFrame
  | EPopFrame
  | EBool of bool
  | EAny
    (** to indicate that the initial value of a mutable let-binding does not
     * matter *)
  | EAbort
    (** exits the program prematurely *)
  | EReturn of expr
  | EFlat of (lident * (ident * expr) list)
    (** contains the name of the type we're building *)
  | EField of (lident * expr * ident)
    (** contains the name of the type we're selecting from *)
  | EWhile of (expr * expr)
  | EBufCreateL of expr list


and branches =
  branch list

and branch =
  pattern * expr

and pattern =
  | PUnit
  | PBool of bool
  | PVar of binder

and var =
  int (** a De Bruijn index *)

and binder = {
  name: ident;
  typ: typ;
  mut: bool;
}

and ident =
  string (** for pretty-printing *)

and lident =
  ident list * ident

and typ =
  | TInt of K.width
  | TBuf of typ
  | TUnit
  | TQualified of lident
  | TBool
  | TAny
  | TArrow of (typ * typ)
      (** t1 -> t2 *)
  | TZ
  | TBound of int
  | TApp of (lident * typ list)

let flatten_arrow =
  let rec flatten_arrow acc = function
    | TArrow (t1, t2) -> flatten_arrow (t1 :: acc) t2
    | t -> t, List.rev acc
  in
  flatten_arrow []

(** Versioned binary writing/reading of ASTs *)

type version = int
  [@@deriving yojson]
let current_version: version = 15

type file = string * program
  [@@deriving yojson]
type binary_format = version * file list
  [@@deriving yojson]


(** Input / output of ASTs *)

let read_file (f: string): file list =
  let contents: binary_format =
    if Filename.check_suffix f ".json" then
      let open Result in
      match binary_format_of_yojson (with_open_in f Yojson.Safe.from_channel) with
      | Ok x ->
          x
      | Error e ->
          Printf.eprintf "Couldn't read from .json file: %s\n" e;
          exit 1
    else
      with_open_in f input_value
  in
  let version, files = contents in
  if version <> current_version then
    failwith "This file is for a different version of KreMLin";
  files

let write_file (files: file list) (f: string): unit =
  with_open_out f (fun oc ->
    output_value oc (current_version, files);
  )

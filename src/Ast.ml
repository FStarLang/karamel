(** Definition of the input format. *)

type program =
  decl list

and decl =
  | Function of ident * binder list * expr

and expr =
  | Var of var
  | Constant of constant
  | Unit
  | App of expr * expr list
  | Let of binder * expr * expr
  | LetMut of binder * expr * expr
  | IfThenElse of expr * expr * expr
  | Sequence of expr * expr
  | Assign of var * expr
  | BufCreate of expr * expr
  | BufRead of expr * expr
  | BufWrite of expr * expr * expr
  | BufSub of expr * expr * expr

and constant =
  | Int of Z.t

and var =
  int (** a De Bruijn index *)

and binder =
  ident * typ

and ident =
  string (** for pretty-printing *)

and typ =
  | Int32
  | Buf of typ


(** The ASTs are versioned *)
type version = int
let current_version: version = 1

(** The format we dump in binary form. *)
type format = version * program

let read_file (f: string): program =
  let ic = open_in f in
  let contents: format = input_value ic in
  close_in ic;
  let version, program = contents in
  if version <> current_version then
    failwith "This file is for an older version of KreMLin";
  program

let write_file (p: program) (f: string): unit =
  let oc = open_out f in
  output_value oc (current_version, p);
  close_out oc

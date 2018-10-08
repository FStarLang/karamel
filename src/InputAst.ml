(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 License. *)

(** Definition of the input format. *)

open Utils
open Common

module K = Constant

(** The input AST. Note: F* doesn't have flat data constructors, so we need to introduce
 * (inefficient) boxing for the sake of interop. Other note: this is using the
 * type [int], which COINCIDENTALLY happens to work on both sides (F* extracts
 * to Z.t, but Z.t's runtime representation is the same as int for small
 * integers). *)

type program =
  decl list
  [@@deriving yojson]

and decl =
  (* Code *)
  | DGlobal of (flag list * lident * int * typ * expr)
  | DFunction of (calling_convention option * flag list * int * typ * lident * binder list * expr)
  (* Types *)
  | DTypeAlias of (lident * flag list * int * typ)
      (** Name, number of parameters (De Bruijn), definition. *)
  | DTypeFlat of (lident * flag list * int * fields_t)
      (** The boolean indicates if the field is mutable *)
  (* Assumed things that the type-checker of KreMLin needs to be aware of *)
  | DExternal of (calling_convention option * flag list * lident * typ)
  | DTypeVariant of (lident * flag list * int * branches_t)
  | DTypeAbstractStruct of lident
      (** Note: this is only used for "assume val" declarations in standalone
       * .fsti files that are marked with [@CAbstractStruct]. Full type
       * definitions marked with the attribute give rise to a DTypeVariant or
       * DTypeFlat with the Common.AbstractStruct flag. The Forward declarations
       * are ignored by the checker, meaning that this declarations will get the
       * same abstract typing, except we remember to emit a forward declaration
       * for it. *)

and fields_t =
  (ident * (typ * bool)) list

and branches_t =
  (ident * fields_t) list

(* Note: in order to maintain backwards-binary-compatibility, please only add
 * constructors at the end of the data type. *)
and expr =
  | EBound of var
  | EQualified of lident
  | EConstant of K.t
  | EUnit
  | EApp of (expr * expr list)
  | ETApp of (expr * typ list)
  | ELet of (binder * expr * expr)
  | EIfThenElse of (expr * expr * expr)
  | ESequence of expr list
  | EAssign of (expr * expr)
    (** left expression can only be a EBound or EOpen *)
  | EBufCreate of (lifetime * expr * expr)
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
     * matter and may not be provided! if you need a dummy value, use EUnit *)
  | EAbort
    (** exits the program prematurely *)
  | EReturn of expr
  | EFlat of (typ * (ident * expr) list)
    (** contains the name of the type we're building *)
  | EField of (typ * expr * ident)
    (** contains the name of the type we're selecting from *)
  | EWhile of (expr * expr)
  | EBufCreateL of (lifetime * expr list)
  | ETuple of expr list
  | ECons of (typ * ident * expr list)
  | EBufFill of (expr * expr * expr)
    (** buffer, value, len *)
  | EString of string
  | EFun of (binder list * expr * typ)
  | EAbortS of string
  | EBufFree of expr
  | EBufCreateNoInit of (lifetime * expr)

and branches =
  branch list

and branch =
  pattern * expr

and pattern =
  | PUnit
  | PBool of bool
  | PVar of binder
  | PCons of (ident * pattern list)
  | PTuple of pattern list
  | PRecord of (ident * pattern) list
  | PConstant of K.t

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
  | TBound of int
  | TApp of (lident * typ list)
  | TTuple of typ list

let flatten_arrow =
  let rec flatten_arrow acc = function
    | TArrow (t1, t2) -> flatten_arrow (t1 :: acc) t2
    | t -> t, List.rev acc
  in
  flatten_arrow []

(** Versioned binary writing/reading of ASTs *)

type version = int
  [@@deriving yojson]
let current_version: version = 27

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
    failwith (Printf.sprintf "The file %s is for version %d; current version of KreMLin is %d" f version current_version);
  files

let read_files = KList.map_flatten read_file

let write_file (files: file list) (f: string): unit =
  with_open_out_bin f (fun oc ->
    output_value oc (current_version, files);
  )

(** Definition of the input format. *)

open Utils

module K = Constant

(** The input AST. Note: F* doesn't have flat data constructors, so we need to introduce
 * (inefficient) boxing for the sake of interop. *)

type program =
  decl list

and decl =
  | DFunction of (typ * ident * binder list * expr)
  | DTypeAlias of (ident * typ)

and expr =
  | EBound of var
  | EOpen of binder
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
  | EBufRead of (expr * expr)
  | EBufWrite of (expr * expr * expr)
  | EBufSub of (expr * expr * expr)
  | EMatch of (expr * branches)
  | EOp of K.op


and branches =
  branch list

and branch =
  pattern * expr

and pattern =
  | PUnit

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
  | TAlias of ident

(** Versioned binary writing/reading of ASTs *)

type version = int
let current_version: version = 1

type file = string * program
type binary_format = version * file list


(** Some visitors for our AST of expressions *)

class virtual ['env, 'result] visitor = object (self)

  (* This method, whose default implementation is the identity,
     can be used to extend the environment when a binding is
     entered. *)
  method extend (env: 'env) (_: binder): 'env =
    env

  (* The main visitor method inspects the structure of [ty] and
     dispatches control to the appropriate case method. *)
  method visit (env: 'env) (e: expr): 'result =
    match e with
    | EBound var ->
        self#ebound env var
    | EOpen binder ->
        self#eopen env binder
    | EQualified lident ->
        self#equalified env lident
    | EConstant c ->
        self#econstant env c
    | EUnit ->
        self#eunit env
    | EApp (e, es) ->
        self#eapp env e es
    | ELet (b, e1, e2) ->
        self#elet env b e1 e2
    | EIfThenElse (e1, e2, e3) ->
        self#eifthenelse env e1 e2 e3
    | ESequence es ->
        self#esequence env es
    | EAssign (e1, e2) ->
        self#eassign env e1 e2
    | EBufCreate (e1, e2) ->
        self#ebufcreate env e1 e2
    | EBufRead (e1, e2) ->
        self#ebufread env e1 e2
    | EBufWrite (e1, e2, e3) ->
        self#ebufwrite env e1 e2 e3
    | EBufSub (e1, e2, e3) ->
        self#ebufsub env e1 e2 e3
    | EMatch (e, branches) ->
        self#ematch env e branches
    | EOp op ->
        self#eop env op

  method virtual ebound: 'env -> var -> 'result
  method virtual eopen: 'env -> binder -> 'result
  method virtual equalified: 'env -> lident -> 'result
  method virtual econstant: 'env -> K.t -> 'result
  method virtual eunit: 'env -> 'result
  method virtual eapp: 'env -> expr -> expr list -> 'result
  method virtual elet: 'env -> binder -> expr -> expr -> 'result
  method virtual eifthenelse: 'env -> expr -> expr -> expr -> 'result
  method virtual esequence: 'env -> expr list -> 'result
  method virtual eassign: 'env -> expr -> expr -> 'result
  method virtual ebufcreate: 'env -> expr -> expr -> 'result
  method virtual ebufread: 'env -> expr -> expr -> 'result
  method virtual ebufwrite: 'env -> expr -> expr -> expr -> 'result
  method virtual ebufsub: 'env -> expr -> expr -> expr -> 'result
  method virtual ematch: 'env -> expr -> branches -> 'result
  method virtual eop: 'env -> K.op -> 'result

end


class ['env] map = object (self)

  inherit ['env, expr] visitor

  method ebound _env var =
    EBound var

  method eopen _env binder =
    EOpen binder

  method equalified _env lident =
    EQualified lident

  method econstant _env constant =
    EConstant constant

  method eunit _env =
    EUnit

  method eapp env e es =
    EApp (self#visit env e, List.map (self#visit env) es)

  method elet env b e1 e2 =
    ELet (b, self#visit env e1, self#visit (self#extend env b) e2)

  method eifthenelse env e1 e2 e3 =
    EIfThenElse (self#visit env e1, self#visit env e2, self#visit env e3)

  method esequence env es =
    ESequence (List.map (self#visit env) es)

  method eassign env e1 e2 =
    EAssign (self#visit env e1, self#visit env e2)

  method ebufcreate env e1 e2 =
    EBufCreate (self#visit env e1, self#visit env e2)

  method ebufread env e1 e2 =
    EBufRead (self#visit env e1, self#visit env e2)

  method ebufwrite env e1 e2 e3 =
    EBufWrite (self#visit env e1, self#visit env e2, self#visit env e3)

  method ebufsub env e1 e2 e3 =
    EBufSub (self#visit env e1, self#visit env e2, self#visit env e3)

  method ematch env e branches =
    EMatch (self#visit env e, self#branches env branches)

  method eop env o =
    EOp o

  method branches env branches =
    List.map (fun (pat, expr) ->
      pat, self#visit env expr
    ) branches

end

(** Input / output of ASTs *)

let read_file (f: string): file list =
  let contents: binary_format = with_open_in f input_value in
  let version, files = contents in
  if version <> current_version then
    failwith "This file is for an older version of KreMLin";
  files

let write_file (files: file list) (f: string): unit =
  with_open_out f (fun oc ->
    output_value oc (current_version, files);
  )

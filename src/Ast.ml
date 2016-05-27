(** Definition of the input format. *)

(** The input AST *)

type program =
  decl list

and decl =
  | DFunction of ident * binder list * expr

and expr =
  | EBound of var
  | EOpen of atom
  | EQualified of lident
  | EConstant of constant
  | EUnit
  | EApp of expr * expr list
  | ELet of binder * expr * expr
  | EIfThenElse of expr * expr * expr
  | ESequence of expr * expr
  | EAssign of expr * expr
    (** left expression can only be a EBound of EOpen *)
  | EBufCreate of expr * expr
  | EBufRead of expr * expr
  | EBufWrite of expr * expr * expr
  | EBufSub of expr * expr * expr

and constant =
  | CInt of Z.t

and var =
  int (** a De Bruijn index *)

and atom =
  Atom.t

and binder =
  ident * typ * bool (** bool is for mutable *)

and ident =
  string (** for pretty-printing *)

and lident =
  ident list * ident

and typ =
  | TInt32
  | TBuf of typ


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
    | EOpen atom ->
        self#eopen env atom
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
    | ESequence (e1, e2) ->
        self#esequence env e1 e2
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

  method virtual ebound: 'env -> var -> 'result
  method virtual eopen: 'env -> atom -> 'result
  method virtual equalified: 'env -> lident -> 'result
  method virtual econstant: 'env -> constant -> 'result
  method virtual eunit: 'env -> 'result
  method virtual eapp: 'env -> expr -> expr list -> 'result
  method virtual elet: 'env -> binder -> expr -> expr -> 'result
  method virtual eifthenelse: 'env -> expr -> expr -> expr -> 'result
  method virtual esequence: 'env -> expr -> expr -> 'result
  method virtual eassign: 'env -> expr -> expr -> 'result
  method virtual ebufcreate: 'env -> expr -> expr -> 'result
  method virtual ebufread: 'env -> expr -> expr -> 'result
  method virtual ebufwrite: 'env -> expr -> expr -> expr -> 'result
  method virtual ebufsub: 'env -> expr -> expr -> expr -> 'result

end


class ['env] map = object (self)

  inherit ['env, expr] visitor

  method ebound _env var =
    EBound var

  method eopen _env atom =
    EOpen atom

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

  method esequence env e1 e2 =
    ESequence (self#visit env e1, self#visit env e2)

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

end


(** Versioned binary writing/reading of ASTs *)

type version = int
let current_version: version = 1

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

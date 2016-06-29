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
  | DGlobal of (ident * typ * expr)

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
  | EBufSub of (expr * expr)
  | EBufBlit of (expr * expr * expr * expr * expr)
  | EMatch of (expr * branches)
  | EOp of (K.op * K.width)
  | ECast of (expr * typ)
  | EPushFrame
  | EPopFrame


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
  mutable mark: int;
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
  | TZ

(** Versioned binary writing/reading of ASTs *)

type version = int
let current_version: version = 4

type file = string * program
type binary_format = version * file list


(** Some visitors for our AST of expressions *)

let binders_of_pat = function
  | PVar b ->
      [ b ]
  | PUnit
  | PBool _ ->
      []

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
    | EBufBlit (e1, e2, e3, e4, e5) ->
        self#ebufblit env e1 e2 e3 e4 e5
    | EBufSub (e1, e2) ->
        self#ebufsub env e1 e2
    | EMatch (e, branches) ->
        self#ematch env e branches
    | EOp (op, w) ->
        self#eop env op w
    | ECast (e, t) ->
        self#ecast env e t
    | EPushFrame ->
        self#epushframe env
    | EPopFrame ->
        self#epopframe env

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
  method virtual ebufblit: 'env -> expr -> expr -> expr -> expr -> expr -> 'result
  method virtual ebufsub: 'env -> expr -> expr -> 'result
  method virtual ematch: 'env -> expr -> branches -> 'result
  method virtual eop: 'env -> K.op -> K.width -> 'result
  method virtual ecast: 'env -> expr -> typ -> 'result
  method virtual epushframe: 'env -> 'result
  method virtual epopframe: 'env -> 'result

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

  method ebufblit env e1 e2 e3 e4 e5 =
    EBufBlit (self#visit env e1, self#visit env e2, self#visit env e3, self#visit env e4, self#visit env e5)

  method ebufsub env e1 e2 =
    EBufSub (self#visit env e1, self#visit env e2)

  method ematch env e branches =
    EMatch (self#visit env e, self#branches env branches)

  method eop _env o w =
    EOp (o, w)

  method ecast env e t =
    ECast (self#visit env e, t)

  method epopframe _env =
    EPopFrame

  method epushframe _env =
    EPushFrame

  method branches env branches =
    List.map (fun (pat, expr) ->
      let binders = binders_of_pat pat in
      let env = List.fold_left self#extend env binders in
      pat, self#visit env expr
    ) branches

  method extend_many env binders =
    List.fold_left self#extend env binders

  method dfunction env ret name binders expr =
    let env = self#extend_many env binders in
    DFunction (ret, name, binders, self#visit env expr)

  method dglobal env name typ expr =
    DGlobal (name, typ, self#visit env expr)

  method dtypealias (_: 'env) name typ =
    DTypeAlias (name, typ)
end

(** Input / output of ASTs *)

let read_file (f: string): file list =
  let contents: binary_format = with_open_in f input_value in
  let version, files = contents in
  if version <> current_version then
    failwith "This file is for a different version of KreMLin";
  files

let write_file (files: file list) (f: string): unit =
  with_open_out f (fun oc ->
    output_value oc (current_version, files);
  )

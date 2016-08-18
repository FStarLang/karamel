(** Definition of the input format. *)

open Utils

module K = Constant

(** The input AST. Note: F* doesn't have flat data constructors, so we need to introduce
 * (inefficient) boxing for the sake of interop. *)

type program =
  decl list
  [@@deriving yojson]

and decl =
  | DFunction of (typ * lident * binder list * expr)
  | DTypeAlias of (lident * typ)
  | DGlobal of (lident * typ * expr)
  | DTypeFlat of (lident * (ident * typ) list)

and expr =
  | EBound of var
  | EOpen of binder
  | EQualified of lident
  | EConstant of K.t
  | EUnit
  | EApp of (expr * expr list)
  | ELet of (binder * expr * expr)
  | EIfThenElse of (expr * expr * expr * typ)
  | ESequence of expr list
  | EAssign of (expr * expr)
    (** left expression can only be a EBound or EOpen *)
  | EBufCreate of (expr * expr)
  | EBufRead of (expr * expr)
  | EBufWrite of (expr * expr * expr)
  | EBufSub of (expr * expr)
  | EBufBlit of (expr * expr * expr * expr * expr)
  | EMatch of (expr * branches * typ)
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
  meta: meta option;
}

and meta =
  | MetaSequence

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

let flatten_arrow =
  let rec flatten_arrow acc = function
    | TArrow (t1, t2) -> flatten_arrow (t1 :: acc) t2
    | t -> t, List.rev acc
  in
  flatten_arrow []

(** Versioned binary writing/reading of ASTs *)

type version = int
  [@@deriving yojson]
let current_version: version = 9

type file = string * program
  [@@deriving yojson]
type binary_format = version * file list
  [@@deriving yojson]


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
    | EIfThenElse (e1, e2, e3, t) ->
        self#eifthenelse env e1 e2 e3 t
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
    | EMatch (e, branches, t) ->
        self#ematch env e branches t
    | EOp (op, w) ->
        self#eop env op w
    | ECast (e, t) ->
        self#ecast env e t
    | EPushFrame ->
        self#epushframe env
    | EPopFrame ->
        self#epopframe env
    | EBool b ->
        self#ebool env b
    | EAny ->
        self#eany env
    | EAbort ->
        self#eabort env
    | EReturn e ->
        self#ereturn env e
    | EFlat (tname, fields) ->
        self#eflat env tname fields
    | EField (tname, e, field) ->
        self#efield env tname e field

  method virtual ebound: 'env -> var -> 'result
  method virtual eopen: 'env -> binder -> 'result
  method virtual equalified: 'env -> lident -> 'result
  method virtual econstant: 'env -> K.t -> 'result
  method virtual eunit: 'env -> 'result
  method virtual eany: 'env -> 'result
  method virtual eabort: 'env -> 'result
  method virtual eapp: 'env -> expr -> expr list -> 'result
  method virtual elet: 'env -> binder -> expr -> expr -> 'result
  method virtual eifthenelse: 'env -> expr -> expr -> expr -> typ -> 'result
  method virtual esequence: 'env -> expr list -> 'result
  method virtual eassign: 'env -> expr -> expr -> 'result
  method virtual ebufcreate: 'env -> expr -> expr -> 'result
  method virtual ebufread: 'env -> expr -> expr -> 'result
  method virtual ebufwrite: 'env -> expr -> expr -> expr -> 'result
  method virtual ebufblit: 'env -> expr -> expr -> expr -> expr -> expr -> 'result
  method virtual ebufsub: 'env -> expr -> expr -> 'result
  method virtual ematch: 'env -> expr -> branches -> typ -> 'result
  method virtual eop: 'env -> K.op -> K.width -> 'result
  method virtual ecast: 'env -> expr -> typ -> 'result
  method virtual epushframe: 'env -> 'result
  method virtual epopframe: 'env -> 'result
  method virtual ebool: 'env -> bool -> 'result
  method virtual ereturn: 'env -> expr -> 'result
  method virtual eflat: 'env -> lident -> (ident * expr) list -> 'result
  method virtual efield: 'env -> lident -> expr -> ident -> 'result

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

  method eabort _env =
    EAbort

  method eany _env =
    EAny

  method eunit _env =
    EUnit

  method eapp env e es =
    EApp (self#visit env e, List.map (self#visit env) es)

  method elet env b e1 e2 =
    ELet (b, self#visit env e1, self#visit (self#extend env b) e2)

  method eifthenelse env e1 e2 e3 t =
    EIfThenElse (self#visit env e1, self#visit env e2, self#visit env e3, t)

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

  method ematch env e branches t =
    EMatch (self#visit env e, self#branches env branches, t)

  method eop _env o w =
    EOp (o, w)

  method ecast env e t =
    ECast (self#visit env e, t)

  method epopframe _env =
    EPopFrame

  method epushframe _env =
    EPushFrame

  method ebool _env b =
    EBool b

  method ereturn env e =
    EReturn (self#visit env e)

  method eflat env tname fields =
    EFlat (tname, self#fields env fields)

  method efield env tname e field =
    EField (tname, self#visit env e, field)

  method fields env fields =
    List.map (fun (ident, expr) -> ident, self#visit env expr) fields

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

  method dtypeflat (_: 'env) name fields =
    DTypeFlat (name, fields)
end

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

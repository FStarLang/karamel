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

and expr' =
  | EBound of var
  | EOpen of (ident * Atom.t)
    (** [ident] for debugging purposes only *)
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
  | EFlat of (ident * expr) list
    (** contains the name of the type we're building *)
  | EField of (expr * ident)
    (** contains the name of the type we're selecting from *)
  | EWhile of (expr * expr)
  | EBufCreateL of expr list

and expr =
  expr' typed

and 'a typed = {
  node: 'a;
  mutable mtyp: typ
    (** Filled in by [Checker] *)
}

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
  mark: int ref;
  meta: meta option;
  atom: Atom.t;
    (** Only makes sense when opened! *)
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
      (** t1 -> t2 *)
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
let current_version: version = 10

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

class virtual ['env, 'result, 'tresult, 'dresult, 'extra] visitor = object (self)

  (* This method, whose default implementation is the identity,
     can be used to extend the environment when a binding is
     entered. *)
  method extend (env: 'env) (_: binder): 'env =
    env

  (* The main visitor method inspects the structure of [e] and
     dispatches control to the appropriate case method. *)
  method visit_e (env: 'env) (e: expr') (mtyp: 'extra): 'result =
    match e with
    | EBound var ->
        self#ebound env mtyp var
    | EOpen (name, atom) ->
        self#eopen env mtyp name atom
    | EQualified lident ->
        self#equalified env mtyp lident
    | EConstant c ->
        self#econstant env mtyp c
    | EUnit ->
        self#eunit env mtyp
    | EApp (e, es) ->
        self#eapp env mtyp e es
    | ELet (b, e1, e2) ->
        self#elet env mtyp b e1 e2
    | EIfThenElse (e1, e2, e3) ->
        self#eifthenelse env mtyp e1 e2 e3
    | ESequence es ->
        self#esequence env mtyp es
    | EAssign (e1, e2) ->
        self#eassign env mtyp e1 e2
    | EBufCreate (e1, e2) ->
        self#ebufcreate env mtyp e1 e2
    | EBufRead (e1, e2) ->
        self#ebufread env mtyp e1 e2
    | EBufWrite (e1, e2, e3) ->
        self#ebufwrite env mtyp e1 e2 e3
    | EBufBlit (e1, e2, e3, e4, e5) ->
        self#ebufblit env mtyp e1 e2 e3 e4 e5
    | EBufSub (e1, e2) ->
        self#ebufsub env mtyp e1 e2
    | EMatch (e, branches) ->
        self#ematch env mtyp e branches
    | EOp (op, w) ->
        self#eop env mtyp op w
    | ECast (e, t) ->
        self#ecast env mtyp e t
    | EPushFrame ->
        self#epushframe env mtyp
    | EPopFrame ->
        self#epopframe env mtyp
    | EBool b ->
        self#ebool env mtyp b
    | EAny ->
        self#eany env mtyp
    | EAbort ->
        self#eabort env mtyp
    | EReturn e ->
        self#ereturn env mtyp e
    | EFlat fields ->
        self#eflat env mtyp fields
    | EField (e, field) ->
        self#efield env mtyp e field
    | EWhile (e1, e2) ->
        self#ewhile env mtyp e1 e2
    | EBufCreateL es ->
        self#ebufcreatel env mtyp es

  method virtual ebound: 'env -> 'extra -> var -> 'result
  method virtual eopen: 'env -> 'extra -> ident -> Atom.t -> 'result
  method virtual equalified: 'env -> 'extra -> lident -> 'result
  method virtual econstant: 'env -> 'extra -> K.t -> 'result
  method virtual eunit: 'env -> 'extra -> 'result
  method virtual eany: 'env -> 'extra -> 'result
  method virtual eabort: 'env -> 'extra -> 'result
  method virtual eapp: 'env -> 'extra -> expr -> expr list -> 'result
  method virtual elet: 'env -> 'extra -> binder -> expr -> expr -> 'result
  method virtual eifthenelse: 'env -> 'extra -> expr -> expr -> expr -> 'result
  method virtual esequence: 'env -> 'extra -> expr list -> 'result
  method virtual eassign: 'env -> 'extra -> expr -> expr -> 'result
  method virtual ebufcreate: 'env -> 'extra -> expr -> expr -> 'result
  method virtual ebufread: 'env -> 'extra -> expr -> expr -> 'result
  method virtual ebufwrite: 'env -> 'extra -> expr -> expr -> expr -> 'result
  method virtual ebufblit: 'env -> 'extra -> expr -> expr -> expr -> expr -> expr -> 'result
  method virtual ebufsub: 'env -> 'extra -> expr -> expr -> 'result
  method virtual ematch: 'env -> 'extra -> expr -> branches -> 'result
  method virtual eop: 'env -> 'extra -> K.op -> K.width -> 'result
  method virtual ecast: 'env -> 'extra -> expr -> 'extra -> 'result
  method virtual epushframe: 'env -> 'extra -> 'result
  method virtual epopframe: 'env -> 'extra -> 'result
  method virtual ebool: 'env -> 'extra -> bool -> 'result
  method virtual ereturn: 'env -> 'extra -> expr -> 'result
  method virtual eflat: 'env -> 'extra -> (ident * expr) list -> 'result
  method virtual efield: 'env -> 'extra -> expr -> ident -> 'result
  method virtual ewhile: 'env -> 'extra -> expr -> expr -> 'result
  method virtual ebufcreatel: 'env -> 'extra -> expr list -> 'result

  method visit_t (env: 'env) (t: typ): 'tresult =
    match t with
    | TInt w ->
        self#tint env w
    | TBuf t ->
        self#tbuf env t
    | TUnit ->
        self#tunit env
    | TQualified lid ->
        self#tqualified env lid
    | TBool ->
        self#tbool env
    | TAny ->
        self#tany env
    | TArrow (t1, t2) ->
        self#tarrow env t1 t2
    | TZ ->
        self#tz env

  method virtual tint: 'env -> K.width -> 'tresult
  method virtual tbuf: 'env -> typ -> 'tresult
  method virtual tunit: 'env ->  'tresult
  method virtual tqualified: 'env -> lident -> 'tresult
  method virtual tbool: 'env -> 'tresult
  method virtual tany: 'env -> 'tresult
  method virtual tarrow: 'env -> typ -> typ -> 'tresult
  method virtual tz: 'env -> 'tresult

  method visit_d (env: 'env) (d: decl): 'dresult =
    match d with
    | DFunction (ret, name, binders, expr) ->
        self#dfunction env ret name binders expr
    | DTypeAlias (name, t) ->
        self#dtypealias env name t
    | DGlobal (name, typ, expr) ->
        self#dglobal env name typ expr
    | DTypeFlat (name, fields) ->
        self#dtypeflat env name fields

  method virtual dfunction: 'env -> typ -> lident -> binder list -> expr -> 'dresult
  method virtual dtypealias: 'env -> lident -> typ -> 'dresult
  method virtual dglobal: 'env -> lident -> typ -> expr -> 'dresult
  method virtual dtypeflat: 'env -> lident -> (ident * typ) list -> 'dresult
end


class ['env] map = object (self)

  inherit ['env, expr', typ, decl, typ] visitor

  method visit env e: expr =
    let mtyp = self#visit_t env e.mtyp in
    let node = self#visit_e env e.node mtyp in
    { node; mtyp }

  method ebound _env _typ var =
    EBound var

  method eopen _env _typ name atom =
    EOpen (name, atom)

  method equalified _env _typ lident =
    EQualified lident

  method econstant _env _typ constant =
    EConstant constant

  method eabort _env _typ =
    EAbort

  method eany _env _typ =
    EAny

  method eunit _env _typ =
    EUnit

  method eapp env _typ e es =
    EApp (self#visit env e, List.map (self#visit env) es)

  method elet env _typ b e1 e2 =
    let b = { b with typ = self#visit_t env b.typ } in
    ELet (b, self#visit env e1, self#visit (self#extend env b) e2)

  method eifthenelse env _typ e1 e2 e3 =
    EIfThenElse (self#visit env e1, self#visit env e2, self#visit env e3)

  method esequence env _typ es =
    ESequence (List.map (self#visit env) es)

  method eassign env _typ e1 e2 =
    EAssign (self#visit env e1, self#visit env e2)

  method ebufcreate env _typ e1 e2 =
    EBufCreate (self#visit env e1, self#visit env e2)

  method ebufread env _typ e1 e2 =
    EBufRead (self#visit env e1, self#visit env e2)

  method ebufwrite env _typ e1 e2 e3 =
    EBufWrite (self#visit env e1, self#visit env e2, self#visit env e3)

  method ebufblit env _typ e1 e2 e3 e4 e5 =
    EBufBlit (self#visit env e1, self#visit env e2, self#visit env e3, self#visit env e4, self#visit env e5)

  method ebufsub env _typ e1 e2 =
    EBufSub (self#visit env e1, self#visit env e2)

  method ematch env _typ e branches =
    EMatch (self#visit env e, self#branches env branches)

  method eop _env _typ o w =
    EOp (o, w)

  method ecast env _typ e t =
    ECast (self#visit env e, self#visit_t env t)

  method epopframe _env _typ =
    EPopFrame

  method epushframe _env _typ =
    EPushFrame

  method ebool _env _typ b =
    EBool b

  method ereturn env _typ e =
    EReturn (self#visit env e)

  method eflat env _typ fields =
    EFlat (self#fields env fields)

  method efield env _typ e field =
    EField (self#visit env e, field)

  method ewhile env _typ e1 e2 =
    EWhile (self#visit env e1, self#visit env e2)

  method ebufcreatel env _typ es =
    EBufCreateL (List.map (self#visit env) es)

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

  method tint _env w =
    TInt w

  method tbuf env t =
    TBuf (self#visit_t env t)

  method tunit _env =
    TUnit

  method tqualified _env lid =
    TQualified lid

  method tbool _env =
    TBool

  method tany _env =
    TAny

  method tarrow env t1 t2 =
    TArrow (self#visit_t env t1, self#visit_t env t2)

  method tz _env =
    TZ

  method binders env binders =
    List.map (fun binder -> { binder with typ = self#visit_t env binder.typ }) binders

  method dfunction env ret name binders expr =
    let binders = self#binders env binders in
    let env = self#extend_many env binders in
    DFunction (ret, name, binders, self#visit env expr)

  method dglobal env name typ expr =
    DGlobal (name, self#visit_t env typ, self#visit env expr)

  method dtypealias env name t =
    DTypeAlias (name, self#visit_t env t)

  method fields_t env fields =
    List.map (fun (name, t) -> name, self#visit_t env t) fields

  method dtypeflat env name fields =
    let fields = self#fields_t env fields in
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

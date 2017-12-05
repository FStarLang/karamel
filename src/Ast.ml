(** The internal, typed AST that we perform all transformations on. *)

module K = Constant

(* We wish to generate a visitor that satisfies the following criteria.
 * - The entry points (e.g. visit_file) take an environment, of type env.
 * - The nodes that are paired with a type (expr, pattern, binder) shall
 *   dispatch onto receiver methods (e.g. visit_EBound, visit_PConst, etc.) that
 *   receive a pair of an environment and the (mapped) type of the subexpression.
 * Our strategy is to generate a sequence of visitors, with hand-written
 * adapters to glue them together, whose composition is our final visitor.
 *)

(* Just like int, float, and other OCaml base types, we generate polymorphic
 * methods for the "base types" of our AST. *)
type calling_convention = Common.calling_convention [@ opaque]
and calling_convention_option = calling_convention option
and atom_t = Atom.t [@ opaque]
and flag = Common.flag [@ opaque]
and flags = flag list
and op = K.op [@ opaque]
and width = K.width [@ opaque]
and lifetime = Common.lifetime [@ opaque]
and constant = K.t [@ opaque]
and ident = string [@ opaque]
and lident = ident list * ident [@ opaque]
  [@@deriving show,
    visitors { variety = "iter"; name = "iter_misc"; polymorphic = true },
    visitors { variety = "reduce"; name = "reduce_misc"; polymorphic = true },
    visitors { variety = "map"; name = "map_misc"; polymorphic = true }]


(* The visitor of types composes with the misc. visitor. *)
type typ =
  | TInt of width
  | TBool
  | TUnit
  | TAny
      (** appears because of casts introduced by erasure... eventually, should
       * not appear! *)
  | TBuf of typ
      (** a buffer in the Low* sense *)
  | TArray of typ * constant
      (** appears when we start hoisting buffer definitions to their enclosing
       * push frame *)
  | TQualified of lident
      (** a reference to a type that has been introduced via a DType *)
  | TArrow of typ * typ
      (** t1 -> t2 *)
  | TApp of lident * typ list
      (** disappears after monomorphization *)
  | TBound of int
      (** appears in type definitions... also disappears after monorphization *)
  | TTuple of typ list
      (** disappears after tuple removal *)
  | TAnonymous of type_def
      (** appears after data type translation to tagged enums *)
  [@@deriving show,
    visitors { variety = "iter"; ancestors = [ "iter_misc" ]; name = "iter_typ" },
    visitors { variety = "reduce"; ancestors = [ "reduce_misc" ]; name = "reduce_typ" },
    visitors { variety = "map"; ancestors = [ "map_misc" ]; name = "map_typ" }]

and type_def =
  | Abbrev of typ
  | Flat of fields_t_opt
  | Variant of branches_t
  | Enum of lident list
  | Union of (ident * typ) list
  | Forward

and fields_t_opt =
  (ident option * (typ * bool)) list

and branches_t =
  (ident * fields_t) list

and fields_t =
  (ident * (typ * bool)) list


(* This type, by virtue of being separated from the recursive definition of expr
 * and pattern, generates no implementation. We provide our own below. *)
type 'a with_type = {
  node: 'a;
  mutable typ: typ
    (** Filled in by [Checker] *)
}
  [@@deriving show]

(* However, as we glue map_expr (that passes around an [env * typ]) to map_typ
 * (that passes around an [env]), we need to indicate that in the process of
 * jumping from expr to typ, we need to drop the second component of the
 * environment. *)
type typ_wo = typ
  [@@deriving show]


(* This adapter provides missing methods for [typ_wo] and [with_type]. Note that
 * inheriting from [map_misc] is important: it lexically shadows the
 * methods for the base types (that were monomorphic) with stronger polymorphic
 * ones, hence allowing [map_typ_adapter] to compose. Without it, there would be
 * a unification conflict between 'env (the type of, say,
 * visit_calling_convention as generated in map_typ) and 'env * typ (the type of
 * visit_calling_convention as generated in map_expr). *)
class ['self] map_typ_adapter = object (self: 'self)

  inherit [_] map_typ
  inherit [_] map_misc

  (* As the visitor of expressions tries to recurse in a [typ], we drop the
   * second component of the pair and visit the type without the second half. *)
  method visit_typ_wo (env, _) t =
    self#visit_typ env t

  (* As we descend into an annotated node, we ignore the second component of the
   * pair we receive (the type of the enclosing expression) and fill the second
   * component of the pair with the mapped type. *)
  method visit_with_type: 'node 'ret.
    (_ -> 'node -> 'ret) -> _ -> 'node with_type -> 'ret with_type =
    fun f (env, _) x ->
      let typ = self#visit_typ env x.typ in
      let node = f (env, typ) x.node in
      { node; typ }
end

class ['self] iter_typ_adapter = object (self: 'self)

  inherit [_] iter_typ
  inherit [_] iter_misc

  method visit_typ_wo (env, _) t =
    self#visit_typ env t

  method visit_with_type: 'node.  (_ -> 'node -> _) -> _ -> 'node with_type -> _ =
    fun f (env, _) x ->
      self#visit_typ env x.typ;
      f (env, x.typ) x.node
end

class virtual ['self] reduce_typ_adapter = object (self: 'self)

  inherit [_] reduce_typ
  inherit [_] reduce_misc

  (* We let the user explain exactly how types and expressions compose. *)
  method virtual expr_plus_typ: _

  method visit_typ_wo (env, _) t =
    self#visit_typ env t

  method visit_with_type: 'node.  (_ -> 'node -> _) -> _ -> 'node with_type -> _ =
    fun f (env, _) x ->
      let a = self#visit_typ env x.typ in
      let b = f (env, x.typ) x.node in
      self#expr_plus_typ a b
end


(* Next, the nodes that are annotated with types. Note that every occurrence of
 * [typ] is actually a [typ_wo] to make sure we strip the second component of
 * the environment. *)
type expr' =
  | EBound of var
  | EOpen of ident * atom_t
    (** [ident] for debugging purposes only *)

  | EOp of op * width
  | EQualified of lident
  | EConstant of constant
  | EUnit
  | EBool of bool
  | EString of string
  | EAny
    (** to indicate that the initial value of a mutable let-binding does not
     * matter *)
  | EAbort of string option
    (** exits the program prematurely *)
  | EIgnore of expr

  | EApp of expr * expr list
  | ETApp of expr * typ_wo list
  | ELet of binder * expr * expr
  | EFun of binder list * expr * typ_wo
  | EIfThenElse of expr * expr * expr
  | ESequence of expr list
  | EAssign of expr * expr
    (** left expression can only be a EBound or EOpen *)

  | EBufCreate of lifetime * expr * expr
    (** initial value, length *)
  | EBufCreateL of lifetime * expr list
  | EBufRead of expr * expr
    (** e1[e2] *)
  | EBufWrite of expr * expr * expr
    (** e1[e2] <- e3 *)
  | EBufSub of expr * expr
    (** e1 + e2 *)
  | EBufBlit of expr * expr * expr * expr * expr
    (** e1 (source), index; e2 (dest), index; len *)
  | EBufFill of expr * expr * expr
  | EPushFrame
  | EPopFrame

  | ETuple of expr list
  | EMatch of expr * branches
  | ECons of ident * expr list

  | ESwitch of expr * (lident * expr) list
  | EEnum of lident
  | EFlat of fields_e_opt
  | EField of expr * ident
    (** The four types above appear after compilation of pattern-matches. *)

  | EBreak
  | EReturn of expr
    (** Dafny generates EReturn nodes; they are currently not synthesized by our
     * internal transformation passes, but may be in the future. *)
  | EWhile of expr * expr
    (** Dafny generates EWhile nodes; we also generate them when desugaring the
     * buffer creation and blitting operations for the Wasm backend. *)
  | EFor of binder * expr * expr * expr * expr
    (** Currently generated when detecting combinators from the [C.Loops]
     * module. We only offer a restricted form of For loops: {[
     *   for (let b = e1; e2; e3) {
     *     ...
     *   }
     * ]}
     * The scope of the binder is the second, third and fourth expressions. *)
  | ECast of expr * typ_wo
  | EComment of string * expr * string
  | EAddrOf of expr

  [@@deriving show,
    visitors { variety = "map"; ancestors = [ "map_typ_adapter" ]; name = "map_expr" },
    visitors { variety = "iter"; ancestors = [ "iter_typ_adapter" ]; name = "iter_expr" },
    visitors { variety = "reduce"; ancestors = [ "reduce_typ_adapter" ]; name = "reduce_expr" } ]

and expr =
  expr' with_type

and fields_e_opt =
  (ident option * expr) list

and branches =
  branch list

and branch =
  (** In the internal AST, the binding structure is done properly for patterns;
   * each branch introduces a set of binders; and the locally nameless approach
   * itself is applied within the pattern (this is useful for non-linear
   * binders, a.k.a. or-patterns). One can open a pattern; then, the binders
   * appear as POpens. Note: I hesitated between [POpen of atom] and [PBinder of
   * binder] for binders; the latter is more convenient for pattern-matching
   * compilation phase, but then one may inadvertently rely on sharing between
   * the [binders]  *)
  binders * pattern * expr

and binders =
  binder list

and pattern' =
  | PUnit
  | PBool of bool
  | PBound of var
  | POpen of ident * atom_t
  | PCons of ident * pattern list
  | PEnum of lident
  | PTuple of pattern list
  | PRecord of (ident * pattern) list
  | PDeref of pattern
  | PConstant of constant
  | PWild

and pattern =
  pattern' with_type

and var =
  int (** a De Bruijn index *)

and binder' = {
  name: ident;
  mut: bool;
  mark: int ref;
  meta: meta option;
  atom: atom_t;
    (** Only makes sense when opened! *)
}

and binder =
  binder' with_type

and meta =
  | MetaSequence


(* Now, we need to add a third layer: the entry points (files, declarations)
 * which take an 'env, not an 'env * typ. We apply the same trick, and note the
 * entry points from decl (un-annotated environments) to expr (annotated
 * environments). *)
type expr_w = expr
  [@@deriving show]

type binder_w = binder
  [@@deriving show]

(* These two methods ensure we recurse with the type. Again, we lexically
 * override the monomorphic methods with polymorphic ones to allow composition.
 * *)
class ['self] map_expr_adapter = object (self: 'self)

  inherit [_] map_expr
  inherit [_] map_misc

  method lift_w: 'a. (_ -> 'a -> 'a) -> _ -> 'a with_type -> 'a with_type =
    fun f env x ->
      let typ = self#visit_typ env x.typ in
      let node = f (env, typ) x.node in
      { node; typ }

  method visit_expr_w =
    self#lift_w self#visit_expr'

  method visit_binder_w =
    self#lift_w self#visit_binder'

  method visit_pattern_w =
    self#lift_w self#visit_pattern'
end

class ['self] iter_expr_adapter = object (self: 'self)

  inherit [_] iter_expr
  inherit [_] iter_misc

  method lift_w: 'a. (_ -> 'a -> _) -> _ -> 'a with_type -> _ =
    fun f env x ->
      self#visit_typ env x.typ;
      f (env, x.typ) x.node;

  method visit_expr_w =
    self#lift_w self#visit_expr'

  method visit_binder_w =
    self#lift_w self#visit_binder'

  method visit_pattern_w =
    self#lift_w self#visit_pattern'
end

class virtual ['self] reduce_expr_adapter = object (self: 'self)

  inherit [_] reduce_expr
  inherit [_] reduce_misc

  method lift_w: 'a. (_ -> 'a -> _) -> _ -> 'a with_type -> _ =
    fun f env x ->
      let a = self#visit_typ env x.typ in
      let b = f (env, x.typ) x.node in
      self#expr_plus_typ a b

  method visit_expr_w =
    self#lift_w self#visit_expr'

  method visit_binder_w =
    self#lift_w self#visit_binder'

  method visit_pattern_w =
    self#lift_w self#visit_pattern'
end


(* We compose everything together by leveraging the _w indirections that wrap up
 * an environment with the type of the sub-node. For nodes that are of the form
 * [foo with_type], we use the higher-order combinator above. For nodes that are
 * an occurrence of [foo with_type], we define another type abbreviation (below)
 * that is identical but contains the [_w] variant so that callers don't have to
 * provide a dummy argument for the type. *)
type program =
  decl list
  [@@deriving show,
    visitors { name = "map_all"; variety = "map"; monomorphic = [ "env" ]; ancestors = ["map_expr_adapter"] },
    visitors { name = "iter"; variety = "iter"; monomorphic = [ "env" ]; ancestors = ["iter_expr_adapter"] },
    visitors { name = "reduce"; variety = "reduce"; monomorphic = [ "env" ]; ancestors = ["reduce_expr_adapter"] }]

and file =
  string * program

and files =
  file list

and decl =
  | DFunction of calling_convention option * flag list * int * typ * lident * binders_w * expr_w
  | DGlobal of flag list * lident * int * typ * expr_w
  | DExternal of calling_convention option * flag list * lident * typ
  | DType of lident * flag list * int * type_def

and binders_w = binder_w list

and fields_e_opt_w =
  (ident option * expr_w) list


(* The final layer overrides a few selected methods to extend the environment
 * with binders. *)
class ['self] names_helper = object (self: 'self)
  
  (* Crossing a binder in expressions. Overridable by the user. *)
  method extend env _ =
    env

  method private extend_wo (env, typ) b =
    self#extend env b, typ

  method private extend_many env bs =
    List.fold_left self#extend env bs

  method private extend_many_wo (env, typ) bs =
    self#extend_many env bs, typ


  (* Crossing a binder in types. Overridable by the user. *)
  method extend_t env =
    env

  method private extend_tmany env n =
    let rec extend e n =
      if n = 0 then
        e
      else
        extend (self#extend_t e) (n - 1)
    in
    extend env n
end


class ['self] map = object (self: 'self)
  inherit [_] map_all
  inherit [_] names_helper

  method! visit_ELet env b e1 e2 =
    let b = self#visit_binder env b in
    let e1 = self#visit_expr env e1 in
    let env = self#extend_wo env b in
    let e2 = self#visit_expr env e2 in
    ELet (b, e1, e2)

  method! visit_EFor env b e1 e2 e3 e4 =
    let b = self#visit_binder env b in
    let e1 = self#visit_expr env e1 in
    let env = self#extend_wo env b in
    let e2 = self#visit_expr env e2 in
    let e3 = self#visit_expr env e3 in
    let e4 = self#visit_expr env e4 in
    EFor (b, e1, e2, e3, e4)

  method! visit_EFun env bs e t =
    let bs = self#visit_binders env bs in
    let env = self#extend_many_wo env bs in
    let e = self#visit_expr env e in
    let t = self#visit_typ_wo env t in
    EFun (bs, e, t)

  method! visit_branch env (bs, p, e) =
    let bs = self#visit_binders env bs in
    let env = self#extend_many_wo env bs in
    let p = self#visit_pattern env p in
    let e = self#visit_expr env e in
    bs, p, e

  method! visit_DType env lid flags n d =
    let lid = self#visit_lident env lid in
    let flags = self#visit_flags env flags in
    let env = self#extend_tmany env n in
    let d = self#visit_type_def env d in
    DType (lid, flags, n, d)

  method! visit_DFunction env cc flags n t lid bs e =
    let cc = self#visit_calling_convention_option env cc in
    let flags = self#visit_flags env flags in
    let env = self#extend_tmany env n in
    let t = self#visit_typ env t in
    let lid = self#visit_lident env lid in
    let bs = self#visit_binders_w env bs in
    let env = self#extend_many env bs in
    let e = self#visit_expr_w env e in
    DFunction (cc, flags, n, t, lid, bs, e)
end


(** More helpers *)

let filter_decls f files =
  List.map (fun (file, decls) -> file, KList.filter_map f decls) files

let iter_decls f files =
  List.iter (fun (_, decls) -> List.iter f decls) files

let with_type typ node =
  { typ; node }

let lid_of_decl = function
  | DFunction (_, _, _, _, lid, _, _)
  | DGlobal (_, lid, _, _, _)
  | DExternal (_, _, lid, _)
  | DType (lid, _, _, _) ->
      lid

let flags_of_decl = function
  | DFunction (_, flags, _, _, _, _, _)
  | DGlobal (flags, _, _, _, _)
  | DType (_, flags, _, _)
  | DExternal (_, flags, _, _) ->
      flags


(** Some visitors for our AST of expressions *)

class virtual ['env] deprecated_map = object (self)

  (* Extend the environment; these methods are meant to be overridden. *)
  method extend (env: 'env) (_: binder): 'env =
    env

  method private extend_many env binders =
    List.fold_left self#extend env binders

  method extend_t (env: 'env): 'env =
    env

  method private extend_tmany env n =
    let rec extend e n =
      if n = 0 then
        e
      else
        extend (self#extend_t e) (n - 1)
    in
    extend env n

  (* Toplevel visitor. *)
  method visit_file (env: 'env) (file: file) =
    let name, decls = file in
    name, List.map (self#visit_d env) decls

  (* Expression visitors. *)
  method visit_e (env: 'env) (e: expr') (typ: 'extra): 'result =
    match e with
    | EBound var ->
        self#ebound env typ var
    | EOpen (name, atom) ->
        self#eopen env typ name atom
    | EQualified lident ->
        self#equalified env typ lident
    | EConstant c ->
        self#econstant env typ c
    | EUnit ->
        self#eunit env typ
    | EString s ->
        self#estring env typ s
    | EApp (e, es) ->
        self#eapp env typ e es
    | ETApp (e, ts) ->
        self#etapp env typ e ts
    | ELet (b, e1, e2) ->
        self#elet env typ b e1 e2
    | EIfThenElse (e1, e2, e3) ->
        self#eifthenelse env typ e1 e2 e3
    | ESequence es ->
        self#esequence env typ es
    | EAssign (e1, e2) ->
        self#eassign env typ e1 e2
    | EBufCreate (l, e1, e2) ->
        self#ebufcreate env typ l e1 e2
    | EBufRead (e1, e2) ->
        self#ebufread env typ e1 e2
    | EBufWrite (e1, e2, e3) ->
        self#ebufwrite env typ e1 e2 e3
    | EBufBlit (e1, e2, e3, e4, e5) ->
        self#ebufblit env typ e1 e2 e3 e4 e5
    | EBufFill (e1, e2, e3) ->
        self#ebuffill env typ e1 e2 e3
    | EBufSub (e1, e2) ->
        self#ebufsub env typ e1 e2
    | EMatch (e, branches) ->
        self#ematch env typ e branches
    | EOp (op, w) ->
        self#eop env typ op w
    | ECast (e, t) ->
        self#ecast env typ e t
    | EPushFrame ->
        self#epushframe env typ
    | EPopFrame ->
        self#epopframe env typ
    | EBool b ->
        self#ebool env typ b
    | EAny ->
        self#eany env typ
    | EAbort s ->
        self#eabort env typ s
    | EBreak ->
        self#ebreak env typ
    | EReturn e ->
        self#ereturn env typ e
    | EFlat fields ->
        self#eflat env typ fields
    | EField (e, field) ->
        self#efield env typ e field
    | EWhile (e1, e2) ->
        self#ewhile env typ e1 e2
    | EBufCreateL (l, es) ->
        self#ebufcreatel env typ l es
    | ECons (cons, es) ->
        self#econs env typ cons es
    | ETuple es ->
        self#etuple env typ es
    | EEnum lid ->
        self#eenum env typ lid
    | ESwitch (e, branches) ->
        self#eswitch env typ e branches
    | EComment (s, e, s') ->
        self#ecomment env typ s e s'
    | EFor (binder, e1, e2, e3, e4) ->
        self#efor env typ binder e1 e2 e3 e4
    | EFun (binders, e, t) ->
        self#efun env typ binders e t
    | EAddrOf e ->
        self#eaddrof env typ e
    | EIgnore e ->
        self#eignore env typ e

  method ebound _env _typ var =
    EBound var

  method eopen _env _typ name atom =
    EOpen (name, atom)

  method equalified _env _typ lident =
    EQualified lident

  method econstant _env _typ constant =
    EConstant constant

  method eabort _env _typ s =
    EAbort s

  method eany _env _typ =
    EAny

  method eunit _env _typ =
    EUnit

  method estring _env _typ s =
    EString s

  method eapp env _typ e es =
    EApp (self#visit env e, List.map (self#visit env) es)

  method etapp env _typ e ts =
    ETApp (self#visit env e, List.map (self#visit_t env) ts)

  method elet env _typ b e1 e2 =
    let b = { b with typ = self#visit_t env b.typ } in
    ELet (b, self#visit env e1, self#visit (self#extend env b) e2)

  method eifthenelse env _typ e1 e2 e3 =
    EIfThenElse (self#visit env e1, self#visit env e2, self#visit env e3)

  method esequence env _typ es =
    ESequence (List.map (self#visit env) es)

  method eassign env _typ e1 e2 =
    EAssign (self#visit env e1, self#visit env e2)

  method ebufcreate env _typ l e1 e2 =
    EBufCreate (l, self#visit env e1, self#visit env e2)

  method ebufread env _typ e1 e2 =
    EBufRead (self#visit env e1, self#visit env e2)

  method ebuffill env _typ e1 e2 e3 =
    EBufFill (self#visit env e1, self#visit env e2, self#visit env e3)

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

  method ebreak _env _typ =
    EBreak

  method eflat env _typ fields =
    EFlat (self#fields env fields)

  method efield env _typ e field =
    EField (self#visit env e, field)

  method ewhile env _typ e1 e2 =
    EWhile (self#visit env e1, self#visit env e2)

  method ebufcreatel env _typ l es =
    EBufCreateL (l, List.map (self#visit env) es)

  method econs env _typ ident es =
    ECons (ident, List.map (self#visit env) es)

  method etuple env _typ es =
    ETuple (List.map (self#visit env) es)

  method eenum _env _typ lid =
    EEnum lid

  method eswitch env _ e branches =
    ESwitch (self#visit env e, List.map (fun (lid, e) ->
      lid, self#visit env e
    ) branches)

  method ecomment env _ s e s' =
    EComment (s, self#visit env e, s')

  method efor env _ b e1 e2 e3 e4 =
    let b = { b with typ = self#visit_t env b.typ } in
    let e1 = self#visit env e1 in
    let env = self#extend env b in
    let e2 = self#visit env e2 in
    let e3 = self#visit env e3 in
    let e4 = self#visit env e4 in
    EFor (b, e1, e2, e3, e4)

  method efun env _ binders expr ret =
    let binders = self#binders env binders in
    let env = self#extend_many env binders in
    EFun (binders, self#visit env expr, self#visit_t env ret)

  method eaddrof env _ e =
    EAddrOf (self#visit env e)

  method eignore env _ e =
    EIgnore (self#visit env e)

  (* Some helpers *)

  method fields env fields =
    List.map (fun (ident, expr) -> ident, self#visit env expr) fields

  method branches env branches =
    List.map (self#branch env) branches

  method branch env (binders, pat, expr) =
    let env = List.fold_left self#extend env binders in
    let binders = List.map (fun b -> { b with typ = self#visit_t env b.typ }) binders in
    binders, self#visit_pattern env pat, self#visit env expr

  (* Patterns *)

  method visit_p env pat t =
    match pat with
    | PUnit ->
        self#punit env
    | PBool b ->
        self#pbool env b
    | PBound b ->
        self#pbound env t b
    | POpen (i, a) ->
        self#popen env t i a
    | PCons (ident, fields) ->
        self#pcons env t ident fields
    | PTuple ps ->
        self#ptuple env t ps
    | PRecord fields ->
        self#precord env t fields
    | PEnum lid ->
        self#penum env t lid
    | PWild ->
        self#pwild env
    | PDeref p ->
        self#pderef env t p
    | PConstant k ->
        self#pconstant env t k

  method punit _env =
    PUnit

  method pderef env _t p =
    PDeref (self#visit_pattern env p)

  method pwild _env =
    PWild

  method pbool _env b =
    PBool b

  method pbound _env _t b =
    PBound b

  method popen _env _t i a =
    POpen (i, a)

  method pcons env _t ident pats =
    PCons (ident, List.map (self#visit_pattern env) pats)

  method ptuple env _t pats =
    PTuple (List.map (self#visit_pattern env) pats)

  method precord env _t fields =
    PRecord (List.map (fun (f, p) -> f, self#visit_pattern env p) fields)

  method penum _env _t lid =
    PEnum lid

  method pconstant _env _t k =
    PConstant k

  (* Types *)

  method visit_t (env: 'env) (t: typ): typ =
    match t with
    | TInt w ->
        self#tint env w
    | TBuf t ->
        self#tbuf env t
    | TArray (t, k) ->
        self#tarray env t k
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
    | TBound i ->
        self#tbound env i
    | TApp (name, args) ->
        self#tapp env name args
    | TTuple ts ->
        self#ttuple env ts
    | TAnonymous t ->
        self#tanonymous env t

  method tint _env w =
    TInt w

  method tbuf env t =
    TBuf (self#visit_t env t)

  method tarray env t k =
    TArray (self#visit_t env t, k)

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

  method tbound _env i =
    TBound i

  method tapp env lid ts =
    TApp (lid, List.map (self#visit_t env) ts)

  method ttuple env ts =
    TTuple (List.map (self#visit_t env) ts)

  method tanonymous env d =
    TAnonymous (self#type_def env None d)


  (* Once types and expressions can be visited, a more generic method that
   * handles the type. *)

  method visit_pattern env p: pattern =
    let typ = self#visit_t env p.typ in
    let node = self#visit_p env p.node typ in
    { node; typ }

  method visit env e: expr =
    let typ = self#visit_t env e.typ in
    let node = self#visit_e env e.node typ in
    { node; typ }


  (* Declarations *)

  method visit_d (env: 'env) (d: decl): 'dresult =
    match d with
    | DFunction (cc, flags, n, ret, name, binders, expr) ->
        self#dfunction env cc flags n ret name binders expr
    | DGlobal (flags, name, n, typ, expr) ->
        self#dglobal env flags name n typ expr
    | DExternal (cc, flags, name, t) ->
        self#dexternal env cc flags name t
    | DType (name, flags, n, d) ->
        self#dtype env name flags n d

  method dtype env name flags n d =
    let env = self#extend_tmany env n in
    DType (name, flags, n, self#type_def env (Some name) d)

  method type_def (env: 'env) (name: lident option) (d: type_def) =
    match d with
    | Flat fields ->
        self#dtypeflat env fields
    | Abbrev t ->
        self#dtypealias env t
    | Variant branches ->
        self#dtypevariant env (Option.must name) branches
    | Enum tags ->
        self#dtypeenum env tags
    | Union ts ->
        self#dtypeunion env ts
    | Forward ->
        self#dforward env

  method binders env binders =
    List.map (fun binder -> { binder with typ = self#visit_t env binder.typ }) binders

  method dfunction env cc flags n ret name binders expr =
    let binders = self#binders env binders in
    let env = self#extend_many env binders in
    let env = self#extend_tmany env n in
    DFunction (cc, flags, n, self#visit_t env ret, name, binders, self#visit env expr)

  method dglobal env flags name n typ expr =
    DGlobal (flags, name, n, self#visit_t env typ, self#visit env expr)

  method dexternal env cc flags name t =
    DExternal (cc, flags, name, self#visit_t env t)

  method dtypealias env t =
    Abbrev (self#visit_t env t)

  method fields_t: 'a. 'env -> (('a * (typ * bool)) list) -> (('a * (typ * bool)) list) =
    fun env fields ->
      List.map (fun (name, (t, mut)) -> name, (self#visit_t env t, mut)) fields

  method dtypeflat env fields =
    let fields = self#fields_t env fields in
    Flat fields

  method dtypevariant env _lid branches =
    Variant (self#branches_t env branches)

  method dtypeenum _env tags =
    Enum tags

  method dforward _env =
    Forward

  method dtypeunion env ts =
    Union (List.map (fun (name, t) -> name, self#visit_t env t) ts)

  method branches_t env branches =
    List.map (fun (ident, fields) -> ident, self#fields_t env fields) branches
end



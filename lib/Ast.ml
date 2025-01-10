(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 and MIT Licenses. *)

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
type calling_convention = Common.calling_convention [@ visitors.opaque]
and calling_convention_option = calling_convention option
and atom_t = Atom.t [@ visitors.opaque]
and flag = Common.flag [@ visitors.opaque]
and flags = flag list
and op = K.op [@ visitors.opaque]
and width = K.width [@ visitors.opaque]
and lifetime = Common.lifetime [@ visitors.opaque]
and constant = K.t [@ visitors.opaque]
and ident = string [@ visitors.opaque]
and z = Z.t [@ opaque]
and poly_comp = K.poly_comp [@ visitors.opaque] [@ show.opaque]
and forward_kind = Common.forward_kind [@ visitors.opaque]
and lident = ident list * ident [@ visitors.opaque]
and valuation = Mark.occurrence * Mark.usage [@ visitors.opaque]
  [@@deriving show,
    visitors { variety = "iter"; name = "iter_misc"; polymorphic = true },
    visitors { variety = "reduce"; name = "reduce_misc"; polymorphic = true },
    visitors { variety = "map"; name = "map_misc"; polymorphic = true }]

let dummy_lid = [], ""

type cg =
  | CgVar of int
  | CgConst of constant

(* From 2016-2024, krml spent eight blissful years not dealing with
   higher-order types, and all was fun and dandy. However, with the arrival of
   Rust-style monomorphization, and the passing of trait methods as function
   pointers before whole-program monomorphization, we now need to deal with
   things such as:

     trait Foo<const K: usize> { fn bar<const L: usize>(x: [u8; K]) -> (); }
     fn f<const K:usize, T: Foo<K>>() { }

   which needs to be translated as:

     fn bar<K, L>(x: [u8; K]) -> ()

     fn f<K: usize, T>(bar_k: <L>(x: [u8; K]) -> ())

   and when instantiating the type scheme of f we need to know not to substitute
   under <L>. *)
and type_scheme = {
  n_cgs: int;
  n: int;
}

(* The visitor of types composes with the misc. visitor. *)
and typ =
  | TInt of width
  | TBool
  | TUnit
  | TAny
      (** appears because of casts introduced by erasure... eventually, should
       * not appear! *)
  | TBuf of typ * bool
      (** a buffer in the Low* sense -- boolean indicates whether it's const or
       * not *)
  | TArray of typ * constant
      (** appears when we start hoisting buffer definitions to their enclosing
       * push frame *)
  | TCgArray of typ * int
      (** for monomorphization of stuff coming from Rust (eurydice) *)
  | TQualified of lident
      (** a reference to a type that has been introduced via a DType *)
  | TArrow of typ * typ
      (** t1 -> t2 *)
  | TApp of lident * typ list
      (** disappears after monomorphization *)
  | TCgApp of typ * cg
      (** typ is either TCgApp, TApp, or TQualified *)
  | TBound of int
      (** appears in type definitions... also disappears after monorphization *)
  | TTuple of typ list
      (** disappears after tuple removal *)
  | TAnonymous of type_def
      (** appears after data type translation to tagged enums *)
  | TPoly of type_scheme * typ
      (** only generated from trait methods in Rust *)
  [@@deriving show,
    visitors { variety = "iter"; ancestors = [ "iter_misc" ]; name = "iter_typ" },
    visitors { variety = "reduce"; ancestors = [ "reduce_misc" ]; name = "reduce_typ" },
    visitors { variety = "map"; ancestors = [ "map_misc" ]; name = "map_typ" }]

and type_def =
  | Abbrev of typ
  | Flat of fields_t_opt
  | Variant of branches_t
  | Enum of (lident * z option) list
  | Union of (ident * typ) list
  | Forward of forward_kind

and fields_t_opt =
  (ident option * (typ * bool)) list

and branches_t =
  branch_t list

and branch_t =
  (ident * fields_t)

and fields_t =
  (ident * (typ * bool)) list

type node_meta =
  | CommentBefore of string
  | CommentAfter of string

and node_meta' = node_meta [@visitors.opaque] [@@deriving show]

(* This type, by virtue of being separated from the recursive definition of expr
 * and pattern, generates no implementation. We provide our own below. *)
type 'a with_type = {
  node: 'a;
  mutable typ: typ;
  meta: node_meta' list;
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
      { node; typ; meta = x.meta }
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

  method visit_typ_wo (env, _) t =
    self#visit_typ env t

  method visit_with_type: 'node.  (_ -> 'node -> _) -> _ -> 'node with_type -> _ =
    fun f (env, _) x ->
      let a = self#visit_typ env x.typ in
      let b = f (env, x.typ) x.node in
      self#plus a b
end

(* Next, the nodes that are annotated with types. Note that every occurrence of
 * [typ] is actually a [typ_wo] to make sure we strip the second component of
 * the environment.
 *
 * Warning: any new node needs to be taken into account in the visitors in src/Helpers.ml *)
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
  | EAbort of typ_wo option * string option
    (** exits the program prematurely; ideally the type of the early return
        should always be there, but sadly we don't always have it, so we do an
        approximation *)
  | EIgnore of expr

  | EApp of expr * expr list
  | ETApp of expr * expr list * expr list * typ_wo list
    (** The arguments are:
      - the head of the application
      - the const generic args (TODO: would be nice to have a way to deal with
        those without those silly diff computations)
      - additional arguments to monomorphize over NOT IN SCOPE in types
      - type arguments *)
  | EPolyComp of poly_comp * typ_wo
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
  | EBufDiff of expr * expr
    (** e1 - e2 *)
  | EBufBlit of expr * expr * expr * expr * expr
    (** e1 (source), index; e2 (dest), index; len *)
  | EBufFill of expr * expr * expr
    (** dst; elt; len *)
  | EBufFree of expr
  | EBufNull
  | EPushFrame
  | EPopFrame

  | ETuple of expr list
  | EMatch of match_flavor * expr * branches
  | ECons of ident * expr list

  | ESwitch of expr * (switch_case * expr) list
  | EEnum of lident
  | EFlat of fields_e_opt
  | EField of expr * ident
    (** The four types above appear after compilation of pattern-matches. *)

  | EBreak
  | EContinue
  | EReturn of expr
    (** Generated, formerly, by Dafny, ages ago. Now also generated by Eurydice,
      and by krml's own -ftail-calls. *)
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
  | EStandaloneComment of string
  | EAddrOf of expr

  [@@deriving show,
    visitors { variety = "map"; ancestors = [ "map_typ_adapter" ]; name = "map_expr" },
    visitors { variety = "iter"; ancestors = [ "iter_typ_adapter" ]; name = "iter_expr" },
    visitors { variety = "reduce"; ancestors = [ "reduce_typ_adapter" ]; name = "reduce_expr" } ]

and expr =
  expr' with_type

and fields_e_opt =
  (ident option * expr) list

and switch_case =
  | SConstant of constant
  | SEnum of lident
  | SWild

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
  | PCons of ident * pattern list (* why are fields not named? *)
  | PEnum of lident
  | PTuple of pattern list
  | PRecord of (ident * pattern) list
      (* here fields are named but this is redundant because F* guarantees they're all present *)
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
  mark: valuation ref;
  meta: meta option;
  atom: atom_t;
    (** Only makes sense when opened! *)
  attempt_inline: bool; (* Whether to attempt inlining, as if this was named uu__... *)
}

and binder =
  binder' with_type

and meta =
  | MetaSequence

and match_flavor = | Checked | Unchecked


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
      { node; typ; meta = x.meta }

  method visit_expr_w env e =
    self#visit_expr (env, e.typ) e

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
      self#plus a b

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
    visitors { name = "iter_all"; variety = "iter"; monomorphic = [ "env" ]; ancestors = ["iter_expr_adapter"] },
    visitors { name = "reduce_all"; variety = "reduce"; monomorphic = [ "env" ]; ancestors = ["reduce_expr_adapter"] }]

and file =
  string * program

and files =
  file list

and decl =
  | DFunction of calling_convention option * flag list * int * int * typ * lident * binders_w * expr_w
  | DGlobal of flag list * lident * int * typ * expr_w
  | DExternal of calling_convention option * flag list * int * int * lident * typ * string list
    (** String list: only for pretty-printing purposes, names of the first few
     * known arguments. *)
  | DType of lident * flag list * int * int * type_def

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

  method! visit_DType env lid flags n_cg n d =
    let lid = self#visit_lident env lid in
    let flags = self#visit_flags env flags in
    let env = self#extend_tmany env n in
    let d = self#visit_type_def env d in
    DType (lid, flags, n_cg, n, d)

  method! visit_DFunction env cc flags n_cg n t lid bs e =
    let cc = self#visit_calling_convention_option env cc in
    let flags = self#visit_flags env flags in
    let env = self#extend_tmany env n in
    let t = self#visit_typ env t in
    let lid = self#visit_lident env lid in
    let bs = self#visit_binders_w env bs in
    let env = self#extend_many env bs in
    let e = self#visit_expr_w env e in
    DFunction (cc, flags, n_cg, n, t, lid, bs, e)

  method! visit_TPoly env ts t =
    TPoly (ts, self#visit_typ (self#extend_tmany env ts.n) t)

  method! visit_ETApp env e es es' ts =
    let ts = List.map (self#visit_typ_wo env) ts in
    let es = List.map (self#visit_expr env) es in
    let es' = List.map (self#visit_expr env) es' in
    let n = match e.typ with
      | TPoly ({ n; _ }, _) -> n
      | _ -> List.length ts
    in
    let env = self#extend_tmany (fst env) n in
    let e = self#visit_expr_w env e in
    ETApp (e, es, es', ts)
end

class ['self] iter = object (self: 'self)
  inherit [_] iter_all
  inherit [_] names_helper

  method! visit_ELet env b e1 e2 =
    self#visit_binder env b;
    self#visit_expr env e1;
    let env = self#extend_wo env b in
    self#visit_expr env e2

  method! visit_EFor env b e1 e2 e3 e4 =
    self#visit_binder env b;
    self#visit_expr env e1;
    let env = self#extend_wo env b in
    self#visit_expr env e2;
    self#visit_expr env e3;
    self#visit_expr env e4

  method! visit_EFun env bs e t =
    self#visit_binders env bs;
    let env = self#extend_many_wo env bs in
    self#visit_expr env e;
    self#visit_typ_wo env t

  method! visit_branch env (bs, p, e) =
    self#visit_binders env bs;
    let env = self#extend_many_wo env bs in
    self#visit_pattern env p;
    self#visit_expr env e

  method! visit_DType env lid flags _n_cg n d =
    self#visit_lident env lid;
    self#visit_flags env flags;
    let env = self#extend_tmany env n in
    self#visit_type_def env d

  method! visit_DFunction env cc flags _n_cg n t lid bs e =
    self#visit_calling_convention_option env cc;
    self#visit_flags env flags;
    let env = self#extend_tmany env n in
    self#visit_typ env t;
    self#visit_lident env lid;
    self#visit_binders_w env bs;
    let env = self#extend_many env bs in
    self#visit_expr_w env e
end

class virtual ['self] reduce = object (self: 'self)
  inherit [_] reduce_all
  inherit [_] names_helper

  method! visit_ELet env b e1 e2 =
    let b' = self#visit_binder env b in
    let e1 = self#visit_expr env e1 in
    let env = self#extend_wo env b in
    let e2 = self#visit_expr env e2 in
    KList.reduce self#plus [ b'; e1; e2 ]

  method! visit_EFor env b e1 e2 e3 e4 =
    let b' = self#visit_binder env b in
    let e1 = self#visit_expr env e1 in
    let env = self#extend_wo env b in
    let e2 = self#visit_expr env e2 in
    let e3 = self#visit_expr env e3 in
    let e4 = self#visit_expr env e4 in
    KList.reduce self#plus [ b'; e1; e2; e3; e4 ]

  method! visit_EFun env bs e t =
    let bs' = self#visit_binders env bs in
    let env = self#extend_many_wo env bs in
    let e = self#visit_expr env e in
    let t = self#visit_typ_wo env t in
    KList.reduce self#plus [ bs'; e; t ]

  method! visit_branch env (bs, p, e) =
    let bs' = self#visit_binders env bs in
    let env = self#extend_many_wo env bs in
    let p = self#visit_pattern env p in
    let e = self#visit_expr env e in
    KList.reduce self#plus [ bs'; p; e ]

  method! visit_DType env lid flags _n_cg n d =
    let lid = self#visit_lident env lid in
    let flags = self#visit_flags env flags in
    let env = self#extend_tmany env n in
    let d = self#visit_type_def env d in
    KList.reduce self#plus [ lid; flags; d ]

  method! visit_DFunction env cc flags _n_cg n t lid bs e =
    let cc = self#visit_calling_convention_option env cc in
    let flags = self#visit_flags env flags in
    let env = self#extend_tmany env n in
    let t = self#visit_typ env t in
    let lid = self#visit_lident env lid in
    let bs' = self#visit_binders_w env bs in
    let env = self#extend_many env bs in
    let e = self#visit_expr_w env e in
    KList.reduce self#plus [ cc; flags; t; lid; bs'; e ]
end


(** More helpers *)

let filter_decls f files =
  List.map (fun (file, decls) -> file, List.filter_map f decls) files

let map_decls f files =
  List.map (fun (file, decls) -> file, List.map f decls) files

let with_type typ node =
  { typ; node; meta = [] }

let flatten_tapp t =
  let rec flatten_tapp cgs t =
    match t with
    | TApp (lid, ts) ->
        lid, ts, List.rev cgs
    | TCgApp (t, cg) ->
        flatten_tapp (cg :: cgs) t
    | TQualified lid ->
        lid, [], List.rev cgs
    | _ ->
        invalid_arg "flatten_tapp"
  in
  flatten_tapp [] t

let fold_tapp (lid, ts, cgs) =
  let t = if ts = [] then TQualified lid else TApp (lid, ts) in
  List.fold_right (fun cg t -> TCgApp (t, cg)) cgs t

let lid_of_decl = function
  | DFunction (_, _, _, _, _, lid, _, _)
  | DGlobal (_, lid, _, _, _)
  | DExternal (_, _, _, _, lid, _, _)
  | DType (lid, _, _, _, _) ->
      lid

let flags_of_decl = function
  | DFunction (_, flags, _, _, _, _, _, _)
  | DGlobal (flags, _, _, _, _)
  | DType (_, flags, _, _, _)
  | DExternal (_, flags, _, _, _, _, _) ->
      flags

let tuple_lid = [ "K" ], ""

let fst3 (x, _, _) = x
let snd3 (_, y, _) = y
let thd3 (_, _, z) = z

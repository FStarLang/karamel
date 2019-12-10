(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 License. *)

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
  | TBuf of typ * bool
      (** a buffer in the Low* sense -- boolean indicates whether it's const or
       * not *)
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
  branch_t list

and branch_t =
  (ident * fields_t)

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
  | EBufFree of expr
  | EPushFrame
  | EPopFrame

  | ETuple of expr list
  | EMatch of expr * branches
  | ECons of ident * expr list

  | ESwitch of expr * (switch_case * expr) list
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
  | DFunction of calling_convention option * flag list * int * typ * lident * binders_w * expr_w
  | DGlobal of flag list * lident * int * typ * expr_w
  | DExternal of calling_convention option * flag list * lident * typ * string list
    (** String list: only for pretty-printing purposes, names of the first few
     * known arguments. *)
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

  method! visit_DType env lid flags n d =
    self#visit_lident env lid;
    self#visit_flags env flags;
    let env = self#extend_tmany env n in
    self#visit_type_def env d

  method! visit_DFunction env cc flags n t lid bs e =
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

  method! visit_DType env lid flags n d =
    let lid = self#visit_lident env lid in
    let flags = self#visit_flags env flags in
    let env = self#extend_tmany env n in
    let d = self#visit_type_def env d in
    KList.reduce self#plus [ lid; flags; d ]

  method! visit_DFunction env cc flags n t lid bs e =
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
  List.map (fun (file, decls) -> file, KList.filter_map f decls) files

let map_decls f files =
  List.map (fun (file, decls) -> file, List.map f decls) files

let with_type typ node =
  { typ; node }

let lid_of_decl = function
  | DFunction (_, _, _, _, lid, _, _)
  | DGlobal (_, lid, _, _, _)
  | DExternal (_, _, lid, _, _)
  | DType (lid, _, _, _) ->
      lid

let flags_of_decl = function
  | DFunction (_, flags, _, _, _, _, _)
  | DGlobal (flags, _, _, _, _)
  | DType (_, flags, _, _)
  | DExternal (_, flags, _, _, _) ->
      flags

(* A minimalistic representation of Rust *)

module Name = struct
  type t = string list [@@ deriving show ]
  let compare = compare
end

type borrow_kind_ = Mut | Shared
[@@deriving show]

type borrow_kind = borrow_kind_ [@ opaque ]
and constant = Constant.t [@ opaque ]
and width = Constant.width [@ opaque ]
and op = Constant.op [@ opaque ]
and name = Name.t [@ visitors.opaque ]

(* Some design choices.
   - We don't intend to perform any deep semantic transformations on this Rust
     representation, but just in case, we retain DeBruijn indices.
   - Rust is an expression-based language, so we don't enforce a distinction
     between statements and expressions -- Rust is not as strict as C in that
     regard. We'll do "the right thing" once we go to a concrete Rust syntax
     tree prior to pretty-printing. *)
and db_index = int [@ opaque ]
[@@deriving show,
    visitors { variety = "map"; name = "map_misc"; polymorphic = true },
    visitors { variety = "reduce"; name = "reduce_misc"; polymorphic = true }]


type typ =
  | Constant of width (* excludes cint, ptrdifft *) [@name "tconstant"]
  | Ref of lifetime option * borrow_kind * typ
  | Vec of typ
  | Array of typ * int [@name "tarray"]
  | Slice of typ (* always appears underneath Ref *)
  | Unit [@name "tunit"]
  | Function of int * typ list * typ
  | Name of name * generic_param list [@name "tname"]
  | Tuple of typ list [@name "ttuple"]
  | App of typ * typ list
  | Bound of db_index
[@@deriving show,
    visitors { variety = "map"; name = "map_typ"; polymorphic = true; ancestors = ["map_misc"] },
    visitors { variety = "reduce"; name = "reduce_typ"; polymorphic = true; ancestors = ["reduce_misc"] }]

and generic_param =
  | Lifetime of lifetime

and lifetime =
  | Label of string

(* Smart constructors *)
let box t =
  App (Name (["Box"], []), [t])

let bool = Constant Bool
let u8 = Constant UInt8
let u16 = Constant UInt16
let u32 = Constant UInt32
let u64 = Constant UInt64
let usize = Constant SizeT

type binding = { name: string; typ: typ; mut: bool; ref: bool (* only for pattern variables *) }
[@@deriving show,
  visitors { variety = "map"; name = "map_binding"; ancestors = [ "map_misc"; "map_typ" ] }]

(* Top-level declarations *)

type array_expr =
  | List of expr list
  | Repeat of expr * expr (* [ e; n ] *)
[@@deriving show,
  visitors { variety = "map"; name = "map_expr" ;
    ancestors = [ "map_binding" ] }]

and expr =
  | Array of array_expr
  | VecNew of array_expr
  | Name of name
  | Borrow of borrow_kind * expr
  | Constant of constant
  | ConstantString of string
  | Let of binding * expr option * expr
  | Call of expr * typ list * expr list
    (** Note that this representation admits empty argument lists -- as opposed
        to Ast which always takes unit *)
  | Unit
  | Panic of string
  | IfThenElse of expr * expr * expr option
  | Assign of expr * expr * typ
  (* In-place update with operator, for instance ^= for xor. *)
  | AssignOp of expr * op * expr * typ
  | As of expr * typ
  | For of binding * expr * expr
  | While of expr * expr
  | Return of expr
  | MethodCall of expr * name * expr list
  | Range of expr option * expr option * bool (* inclusive? *)
  | Struct of struct_name * (string * expr) list
  | Match of expr * typ * match_arm list
  | Tuple of expr list

  (* Place expressions *)
  | Var of db_index
  | Open of open_var
  | Index of expr * expr
  (* The type corresponds to the structure we are accessing.
     We will store None when accessing a native Rust tuple,
     corresponding to an array slice *)
  | Field of expr * string * typ option

  (* Operator expressions *)
  | Operator of op
  | Deref of expr

and match_arm = binding list * pat * expr

(* FIXME: could not reuse constructors like Struct, Var, and Open, using
   [@name "StructP"] to avoid conflicts -- this resulted in typing errors in
   the generated visitors code *)
and pat =
  | Literal of constant
  | Wildcard
  | TupleP of pat list
  | StructP of struct_name * (string * pat) list
  | VarP of db_index
  | OpenP of open_var

(* In the Rust grammar, both variants and structs are covered by the struct
  case. We disambiguate between the two *)
and struct_name =
  [ `Struct of name | `Variant of name * string ] [@ opaque]

and open_var = {
  name: string;
  atom: atom_t
}

and atom_t = Atom.t [@ visitors.opaque]

(* Smart constructors *)
let box_new (e: array_expr) =
  let optimize_size_one = function
    | Repeat(e_init, Constant (_, "1")) ->
        VecNew (List [e_init])
    | e_init ->
        VecNew e_init
  in
  MethodCall (optimize_size_one e, ["into_boxed_slice"], [])

(* e[..] *)
let slice_of_array e =
  Index (Array e, Range (None, None, false))

type visibility = Pub | PubCrate

type meta = {
  visibility: visibility option;
  comment: string;
  attributes: string list;
}

(* TODO: visitors incompatible with inline records *)
type decl =
  | Function of {
    name: name;
    type_parameters: int;
    parameters: binding list;
    return_type: typ;
    body: expr;
    meta: meta;
    inline: bool;
    generic_params: generic_param list;
  }
  | Constant of {
    name: name;
    typ: typ;
    body: expr;
    meta: meta;
  }
  | Enumeration of {
    name: name;
    items: item list;
    derives: trait list;
    meta: meta;
    generic_params: generic_param list;
  }
  | Struct of {
    name: name;
    fields: struct_field list;
    (* FIXME: why have a distinguished list of derives rather than shoving them in the (new)
       attributes field of meta? *)
    derives: trait list;
    meta: meta;
    generic_params: generic_param list;
  }
  | Alias of {
    name: name;
    body: typ;
    generic_params: generic_param list;
    meta: meta;
  }
  (* We need to keep assumed/external functions to perform mutability inference
     at the MiniRust level. However, these nodes will not be printed at code
     generation *)
  | Assumed of {
    name: name;
    parameters: typ list;
    return_type: typ;
  }

and item =
  (* Not supporting tuples yet *)
  string * struct_field list option

and struct_field = {
  name: string;
  typ: typ;
  visibility: visibility option;
}

and trait =
  | PartialEq
  | Clone
  | Copy
  | Custom of string

(* Some visitors for name management *)

module DeBruijn = struct

  (* A usable map where the user can hook up to extend, called every time a new
     binding is added to the environment *)
  class ['self] map = object (self: 'self)
    inherit [_] map_expr as _super

    (* To be overridden by the user *)
    method extend env _ = env

    (* We list all binding nodes and feed those binders to the environment *)
    method! visit_Let env b e1 e2 =
      let e1 = Option.map (self#visit_expr env) e1 in
      let e2 = self#visit_expr (self#extend env b) e2 in
      Let (b, e1, e2)

    method! visit_For env b e1 e2 =
      let e1 = self#visit_expr env e1 in
      let e2 = self#visit_expr (self#extend env b) e2 in
      For (b, e1, e2)

    method! visit_Match env e t branches =
      let e = self#visit_expr env e in
      let branches = List.map (fun (bs, p, e) ->
        let env = List.fold_left self#extend env bs in
        let p = self#visit_pat env p in
        let e = self#visit_expr env e in
        bs, p, e
      ) branches in
      Match (e, t, branches)
  end

  class map_counting = object
    (* The environment [i] has type [int]. *)
    inherit [_] map

    (* The environment [i] keeps track of how many binders have been
       entered. It is incremented at each binder. *)
    method! extend (i: int) (_: binding) =
      i + 1
  end

  class lift (k: int) = object
    inherit map_counting
    (* A local variable (one that is less than [i]) is unaffected;
       a free variable is lifted up by [k]. *)
    method! visit_VarP i j =
      if j < i then
        VarP j
      else
        VarP (j + k)

    method! visit_Var i j =
      if j < i then
        Var j
      else
        Var (j + k)
  end

  class close (a: Atom.t) (e: expr) = object
    inherit map_counting

    method! visit_Open i ({ atom; _ } as v) =
      if Atom.equal a atom then
        (new lift i)#visit_expr 0 e
      else
        Open v
  end

  class close_p (a: Atom.t) (e: pat) = object
    inherit map_counting

    method! visit_OpenP i ({ atom; _ } as v) =
      if Atom.equal a atom then
        (new lift i)#visit_pat 0 e
      else
        OpenP v
  end

  class subst e2 = object
    inherit map_counting

    method! visit_Var i j =
      if j = i then
        (new lift i)#visit_expr 0 e2
      else
        Var (if j < i then j else j - 1)
  end

  class subst_p e2 = object
    inherit map_counting

    method! visit_VarP i j =
      if j = i then
        (new lift i)#visit_pat 0 e2
      else
        VarP (if j < i then j else j - 1)
  end

end

(* Lift `expr` by `k` places so as to place it underneath `k` additional
   binders. *)
let lift (k: int) (expr: expr): expr =
  if k = 0 then
    expr
  else
    (new DeBruijn.lift k)#visit_expr 0 expr

let lift_p (k: int) (pat: pat): pat =
  if k = 0 then
    pat
  else
    (new DeBruijn.lift k)#visit_pat 0 pat

(* Close `a`, replacing it on the fly with `e2` in `e1` *)
let close a e2 e1 =
  (new DeBruijn.close a e2)#visit_expr 0 e1

(* Close `a`, replacing it on the fly with `p2` in `p1` *)
let close_p a e2 e1 =
  (new DeBruijn.close_p a e2)#visit_pat 0 e1

let close_many bs e1 =
  List.fold_left (fun e1 b -> close b (Var 0) (lift 1 e1)) e1 bs

let close_many_p bs e1 =
  List.fold_left (fun e1 b -> close_p b (VarP 0) (lift_p 1 e1)) e1 bs

let close_branch atoms (bs, p, e) =
  bs, close_many_p atoms p, close_many atoms e

(* Substitute `e2` for bound variable `i` in `e1` *)
let subst e2 i e1 =
  (new DeBruijn.subst e2)#visit_expr i e1

(* Substitute `p2` for bound pattern variable `i` in `p1` *)
let subst_p e2 i e1 =
  (new DeBruijn.subst_p e2)#visit_pat i e1

(* Open b in e2, replacing occurrences of a bound variable with the
   corresponding atom. *)
let open_ (b: binding) e2 =
  let atom = Atom.fresh () in
  atom, subst (Open { atom; name = b.name }) 0 e2

let open_many binders term =
  List.fold_right (fun binder (acc, term) ->
    let atom, term = open_ binder term in
    atom :: acc, term
  ) binders ([], term)

let open_branch (bs, pat, expr) =
  List.fold_right (fun binder (bs, pat, expr) ->
    let b, expr = open_ binder expr in
    let pat =
      subst_p (OpenP { name = binder.name; atom = b }) 0 pat
    in
    b :: bs, pat, expr
  ) bs ([], pat, expr)

(* Helpers *)

let name_of_decl (d: decl) =
  match d with
  | Alias { name; _ }
  | Enumeration { name; _ }
  | Struct { name; _ }
  | Function { name; _ }
  | Constant { name; _ }
  | Assumed {name; _ } ->
      name

let zero_usize: expr = Constant (Constant.SizeT, "0")

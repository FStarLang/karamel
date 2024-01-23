(* A minimalistic representation of Rust *)

type borrow_kind_ = Mut | Shared
[@@deriving show]

type borrow_kind = borrow_kind_ [@ opaque ]
and constant = Constant.t [@ opaque ]
and op = Constant.op [@ opaque ]
and name = string list [@ opaque ]

(* Some design choices.
   - We don't intend to perform any deep semantic transformations on this Rust
     representation, but just in case, we retain DeBruijn indices.
   - Rust is an expression-based language, so we don't enforce a distinction
     between statements and expressions -- Rust is not as strict as C in that
     regard. We'll do "the right thing" once we go to a concrete Rust syntax
     tree prior to pretty-printing. *)
and db_index = int [@ opaque ]
[@@deriving show,
    visitors { variety = "map"; name = "map_misc"; polymorphic = true }]

type lifetime =
  | Label of string
[@@deriving show]

type typ_ =
  | Constant of Constant.width (* excludes cint, ptrdifft *)
  | Ref of lifetime option * borrow_kind * typ_
  | Vec of typ_
  | Array of typ_ * int
  | Slice of typ_ (* always appears underneath Ref *)
  | Unit
  | Function of int * typ_ list * typ_
  | Name of name
  | Tuple of typ_ list
  | App of typ_ * typ_ list
  | Bound of db_index
[@@deriving show]

type typ = typ_ [@ opaque ]
[@@deriving show,
    visitors { variety = "map"; name = "map_typ"; polymorphic = true },
    visitors { variety = "reduce"; name = "reduce_typ"; polymorphic = true }]

let bool = Constant Bool
let u32 = Constant UInt32
let usize = Constant SizeT

type binding = { name: string; typ: typ; mut: bool }
[@@deriving show,
  visitors { variety = "map"; name = "map_binding";
    ancestors = [ "map_misc"; "map_typ" ] }]

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
  | Let of binding * expr * expr
  | Call of expr * typ list * expr list
    (** Note that this representation admits empty argument lists -- as opposed
        to Ast which always takes unit *)
  | Unit
  | Panic of string
  | IfThenElse of expr * expr * expr option
  | Assign of expr * expr
  | As of expr * typ
  | For of binding * expr * expr
  | While of expr * expr
  | MethodCall of expr * name * expr list
  | Range of expr option * expr option * bool (* inclusive? *)

  (* Place expressions *)
  | Var of db_index
  | Index of expr * expr
  | Field of expr * string

  (* Operator expressions *)
  | Operator of op
  | Deref of expr

(* TODO: visitors incompatible with inline records *)
type decl =
  | Function of {
    name: name;
    type_parameters: int;
    parameters: binding list;
    return_type: typ;
    body: expr;
    public: bool;
    inline: bool;
  }
  | Constant of {
    name: name;
    typ: typ;
    body: expr;
    public: bool;
  }
  | Enumeration of {
    name: name;
    items: item list;
    public: bool;
  }
  | Struct of {
    name: name;
    fields: struct_field list;
    public: bool;
    generic_params: generic_param list;
  }

and item =
  (* Not supporting tuples yet *)
  name * struct_field list option

and generic_param =
  | Lifetime of lifetime

and struct_field =
  string * typ

(* Some visitors for name management *)

(* A usable map where the user can hook up to extend, called every time a new
   binding is added to the environment *)
class ['self] map = object (self: 'self)
  inherit [_] map_expr as super

  (* To be overridden by the user *)
  method extend env _ = env

  (* We list all binding nodes and feed those binders to the environment *)
  method! visit_Let env b e1 e2 =
    super#visit_Let (self#extend env b) b e1 e2

  method! visit_For env b e1 e2 =
    super#visit_For (self#extend env b) b e1 e2
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
  method! visit_Var i j =
    if j < i then
      Var j
    else
      Var (j + k)
end

let lift (k: int) (expr: expr): expr =
  if k = 0 then
    expr
  else
    (new lift k)#visit_expr 0 expr

(* Helpers *)

let name_of_decl (d: decl) =
  match d with
  | Enumeration { name; _ }
  | Struct { name; _ }
  | Function { name; _ }
  | Constant { name; _ } ->
      name

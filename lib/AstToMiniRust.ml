(* Low* to Rust backend *)

module LidMap = Idents.LidMap

(* Location information *)

type location = {
  curr_func: Ast.lident;
}

let ploc b { curr_func } = PrintAst.Ops.plid b curr_func

let empty_loc = { curr_func = [], "" }

(* Helpers *)

module H = struct

  let add (e1: MiniRust.expr) (e2: MiniRust.expr): MiniRust.expr =
    match e1, e2 with
    | Constant (_, "0"), _ -> e2
    | _, Constant (_, "0") -> e1
    | _, _ -> Call (Operator Add, [], [ e1; e2 ])

  let sub (e1: MiniRust.expr) (e2: MiniRust.expr): MiniRust.expr =
    match e1, e2 with
    | _, Constant (_, "0") -> e1
    | _, _ -> Call (Operator Sub, [], [ e1; e2 ])

  let usize i: MiniRust.expr =
    Constant (SizeT, string_of_int i)

  let range_with_len start len: MiniRust.expr =
    Range (Some start, Some (add start len), false)

  let wrapping_operator_opt = function
    | Constant.Add -> Some "wrapping_add"
    | Div -> Some "wrapping_div"
    | Mult -> Some "wrapping_mul"
    | Neg -> Some "wrapping_neg"
    | Mod -> Some "wrapping_rem"
    | BShiftL -> Some "wrapping_shl"
    | BShiftR -> Some "wrapping_shr"
    | Sub -> Some "wrapping_sub"
    | _ -> None

  let wrapping_operator o =
    Option.get (wrapping_operator_opt o)

  let is_wrapping_operator o =
    wrapping_operator_opt o <> None

  let is_const (e: MiniRust.expr) =
    match e with
    | MiniRust.Constant _ -> true
    | _ -> false

  let assert_const (e: MiniRust.expr) =
    match e with
    | MiniRust.Constant (_, s) -> int_of_string s
    | _ -> failwith "unexpected: assert_const not const"

end

(* Rust's ownership system forbids raw pointer manipulations, meaning that Low*'s "EBufSub"
   operation cannot be compiled as a pointer addition. Instead, we choose to compile it as
   `split_at_mut`, a compilation scheme that entails several limitations.
   - Since the length information is not available to us (it's erased by the time we get here), we
     split on the offset and retain the history of how a given variable was split. Consider the
     following sample program, which sub-divides an array of length 16 into four equal parts -- a
     typical usage in Low*.
     ```
     let x0 = x + 0
     let x1 = x + 8
     let x2 = x + 4
     let x3 = x + 12
     ```
     we compile the first line as:
     ```
     let xr0 = x.split_at_mut(0)
     ```
     and retain the following split tree:

              xr0, 0

     at that point, a *usage* of x0 compiles to `xr0.1` (the right component of xr0).

     Then, we compile xr1 as follows:
     ```
     let xr1 = xr0.1.split_at_mut(8)
     ```

     This updates the split tree of x as follows

              xr0, 0
                  \
                  xr1, 8

     At that stage, note that a *usage* of x0 compiles to `xr1.0`, while a usage of x1 compiles to
     `xr1.1`. We continue with the third split
     ```
     let xr2 = xr1.0.split_at_mut(4)
     ```

     This updates the split tree of `x`:

              xr0, 0
               \
               xr1, 8
             /
            xr2, 4

    At that stage, x0 compiles to xr2.0, x1 compiles to xr1.1, and x2 compiles to xr2.1. The final
    split updates the split tree of x as follows:

              xr0, 0
               \
               xr1, 8
             /      \
            xr2, 4  xr3, 12

  - In order to avoid keeping downwards pointers in the environment from the split tree of `x` down
    to the various xri, the split tree contains only indices, and each one of the xri remembers its
    own position in the tree in the form of a `path`.

  - In order to compute a usage of xri, it suffices to:
    - Lookup xri's path in the tree
    - Find the nearest variable whose path is of the form path(xri) ++ (r ++ l* )? -- i.e. the path
      of xri, followed by a right component, followed by a series of left components.
    - Select the right or left component of that variable, according to the search path above.

  - This compilation scheme obviously does not work if the original program does something like:
    ```
    let x0 = x + 4
    x[4] = ...
    ```
    this will throw a runtime exception in Rust -- in a sense, our compilation scheme is optimistic

  - This compilation scheme has been enhanced to deal with a very simple language of indices, which
    includes constants and addition of constants to terms. This could definitely be improved.

  - In case this does not work, the programmer can always modify the original Low* code.
*)

module Splits = struct
  type leveled_expr = int * MiniRust.expr
    [@@deriving show]

  let equalize (l1, e1) (l2, e2) =
    let l = max l1 l2 in
    let e1 = MiniRust.lift (l - l1) e1 in
    let e2 = MiniRust.lift (l - l2) e2 in
    l, e1, e2

  (* We retain the depth of the environment at the time non-constant indices were recorded, in order
     to be able to compare them properly. *)
  let term_eq e1 e2 =
    let _, e1, e2 = equalize e1 e2 in
    e1 = e2

  (* A super simple grammar of symbolic terms to be compared abstractly *)
  type index =
    | Constant of int
    | Add of leveled_expr * int
    [@@deriving show]

  (* l current length of the environment *)
  let index_of_expr (l: int) (e_ofs: MiniRust.expr) (t_ofs: MiniRust.typ): index =
    match e_ofs with
    | Constant (_, n) -> Constant (int_of_string n)
    | MethodCall (e1, [ "wrapping_add" ], [ Constant (_, n) ])
    | MethodCall (Constant (_, n), [ "wrapping_add" ], [ e1 ]) ->
        if t_ofs = Constant SizeT then
          Add ((l, e1), int_of_string n)
        else
          Add ((l, As (e1, Constant SizeT)), int_of_string n)
    | _ ->
        if t_ofs = Constant SizeT then
          Add ((l, e_ofs), 0)
        else
          Add ((l, As (e_ofs, Constant SizeT)), 0)

  (* l current length of the environment *)
  let expr_of_index (l: int) (e: index): MiniRust.expr =
    match e with
    | Constant i ->
        Constant (SizeT, string_of_int i)
    | Add ((l', e), 0) ->
        let e = MiniRust.lift (l - l') e in
        e
    | Add ((l', e), i) ->
        let e = MiniRust.lift (l - l') e in
        Call (Operator Add, [], [ e; Constant (SizeT, string_of_int i) ])

  let gte (loc: location) i1 i2 =
    match i1, i2 with
    | Constant i1, Constant i2 ->
        i1 >= i2
    | Add (e1, i1), Add (e2, i2) when term_eq e1 e2 ->
        i1 >= i2
    | Add (_e1, i1), Constant i2 ->
        (* operations are homogenous, meaning e1 must have type usize/u32, meaning e1 >= 0 *)
        i1 >= i2
    | Constant i1, Add (e2, i2) ->
        (* TODO: proper warning system *)
        KPrint.bprintf "%a: WARN: cannot compare constant %d and %a + %d\n"
          ploc loc i1 PrintMiniRust.pexpr (snd e2) i2;
        true
    | Add (e1, i1), Add (e2, i2) ->
        (* TODO: proper warning system *)
        KPrint.bprintf "%a: WARN: Cannot compare %a@%d + %d and %a@%d + %d\n"
          ploc loc
          PrintMiniRust.pexpr (snd e1) (fst e1) i1
          PrintMiniRust.pexpr (snd e2) (fst e2) i2;
        true

  let sub (loc: location) i1 i2 =
    match i1, i2 with
    | Constant i1, Constant i2 ->
        Constant (i1 - i2)
    | Add (e1, i1), Add (e2, i2) when term_eq e1 e2 ->
        Constant (i1 - i2)
    | Add (e1, i1), Constant i2 ->
        Add (e1, i1 - i2)
    | Constant i1, Add ((l2, e2), i2) ->
        KPrint.bprintf "%a: WARN: Cannot subtract constant %d and %a + %d\n\
          assuming monotonically increasing indices, this may cause runtime failures\n"
          ploc loc i1 PrintMiniRust.pexpr e2 i2;
        (* i1 - (e2 + i2) *)
        Add ((l2, H.sub (H.usize i1) (H.add e2 (H.usize i2))), 0)
    | Add (e1, i1), Add (e2, i2) ->
        let l, e1, e2 = equalize e1 e2 in
        KPrint.bprintf "%a: WARN: Cannot subtract constant %a@%d + %d and %a@%d + %d\n\
          assuming monotonically increasing indices, this may cause runtime failures\n"
          ploc loc
          PrintMiniRust.pexpr e1 l i1
          PrintMiniRust.pexpr e2 l i2;
        (* (e1 + i1) - (e2 + i2) *)
        Add ((l, H.sub (H.add e1 (H.usize i1)) (H.add e2 (H.usize i2))), 0)

  (* A binary search tree that records the splits that have occured *)
  type tree =
    | Node of index * tree * tree
    | Leaf
    [@@deriving show]

  type path_elem = Left | Right
    [@@deriving show]

  let string_of_path_elem = function
    | Left -> "0"
    | Right -> "1"

  (* A path from the root into a node of the tree *)
  type path = path_elem list
    [@@deriving show]

  type root_or_path =
    | Root
    | Path of path
    [@@deriving show]

  type info = {
    tree: tree;
      (* This variable (originally a "buffer") has been successively split at those indices *)
    path: (MiniRust.db_index * path) option;
      (* This variable "splits" db_index after path consecutive splits *)
  }

  let empty = { tree = Leaf; path = None }

  (* The variable with `info` is being split at `index` *)
  let split loc l info index: info * path * MiniRust.expr =
    let rec split tree index ofs =
      match tree with
      | Leaf ->
          Node (index, Leaf, Leaf), [], ofs
      | Node (index', t1, t2) ->
          if gte loc index index' then
            let t2, path, ofs = split t2 index (sub loc index index') in
            Node (index', t1, t2), Right :: path, ofs
          else
            let t1, path, ofs = split t1 index ofs in
            Node (index', t1, t2), Left :: path, ofs
    in
    let tree, path, ofs = split info.tree index index in
    { info with tree }, path, expr_of_index l ofs

  let find_zero tree =
    let rec find_zero path tree =
      match tree with
      | Leaf -> None
      | Node (Constant 0, _, _) ->
          Some path
      | Node (_, t1, _) ->
          find_zero (Left :: path) t1
    in
    find_zero [] tree

  (* We are trying to access a variable whose position in the tree was originally p1 -- however,
     many more splits may have occurred since this variable was defined. Does p2 provide a way to
     access p1, and if so, via which side? *)
  let accessible_via p1 p2: path_elem option =
    match p1 with
    | Root ->
        if List.for_all ((=) Left) p2 then
          Some Left
        else
          None
    | Path p1 ->
        let l1 = List.length p1 in
        let l2 = List.length p2 in
        if l2 < l1 then
          None
        else
          let p2_prefix, p2_suffix = KList.split l1 p2 in
          if p2_prefix <> p1 then
            None
          else
            match p2_suffix with
            | [] ->
                Some Right
            | Right :: p2_suffix when List.for_all ((=) Left) p2_suffix ->
                Some Left
            | _ ->
                None
end


(* Environments *)

module NameSet = Set.Make(struct
  type t = string list
  let compare = compare
end)

type env = {
  decls: (MiniRust.name * MiniRust.typ) LidMap.t;
  global_scope: NameSet.t;
  types: MiniRust.name LidMap.t;
  vars: (MiniRust.binding * Splits.info) list;
  prefix: string list;
  heap_structs: Idents.LidSet.t;
  pointer_holding_structs: Idents.LidSet.t;
  struct_fields: MiniRust.struct_field list LidMap.t;
  location: location;
}

let empty heap_structs pointer_holding_structs = {
  decls = LidMap.empty;
  global_scope = NameSet.empty;
  types = LidMap.empty;
  vars = [];
  prefix = [];
  struct_fields = LidMap.empty;
  heap_structs;
  pointer_holding_structs;
  location = empty_loc;
}

let locate env curr_func = { env with location = { curr_func } }

let push env (b: MiniRust.binding) =
  (* KPrint.bprintf "Pushing %s to environment at type %a\n" b.name PrintMiniRust.ptyp b.typ; *)
  { env with vars = (b, Splits.empty) :: env.vars }

let push_with_info env b = { env with vars = b :: env.vars }

let push_decl env name t =
  assert (not (LidMap.mem name env.decls));
  { env with decls = LidMap.add name t env.decls }

let push_type env name t =
  assert (not (LidMap.mem name env.types));
  { env with types = LidMap.add name t env.types }

let lookup env v = List.nth env.vars v

let lookup_decl env name =
  LidMap.find name env.decls

let lookup_type env name =
  LidMap.find name env.types

let debug env =
  List.iteri (fun i ((b: MiniRust.binding), info) ->
    let open MiniRust in
    let open Splits in
    KPrint.bprintf "%d\t %s: %s\n  tree = %s\n  path = %s\n"
      i b.name (show_typ b.typ)
      (show_tree info.tree)
      (match info.path with
      | None -> ""
      | Some (v, p) -> KPrint.bsprintf "%d -- %s" v (show_path p))
  ) env.vars

let compress_prefix prefix =
  let depth = !Options.depth in
  let prefix, last = KList.split_at_last prefix in
  if List.length prefix <= depth then
    prefix @ [ last ]
  else
    let path, prefix = KList.split depth prefix in
    path @ [ String.concat "_" (prefix @ [ last ]) ]


(* Types *)

let translate_unknown_lid (m, n) =
  let m = compress_prefix m in
  List.map String.lowercase_ascii m @ [ n ]

let borrow_kind_of_bool _b: MiniRust.borrow_kind =
  Shared

type config = {
  box: bool;
  lifetime: MiniRust.lifetime option;
}

let default_config = {
  box = false;
  lifetime = None;
}

let rec translate_type_with_config (env: env) (config: config) (t: Ast.typ): MiniRust.typ =
  match t with
  | TInt w -> Constant w
  | TBool -> Constant Bool
  | TUnit -> Unit
  | TAny -> failwith "unexpected: [type] no casts in Low* -> Rust"
  | TBuf (t, b) ->
      if config.box then
        MiniRust.box (Slice (translate_type_with_config env config t))
        (* Vec (translate_type_with_config env config t) *)
      else
        Ref (config.lifetime, borrow_kind_of_bool b, Slice (translate_type_with_config env config t))
  | TArray (t, c) -> Array (translate_type_with_config env config t, int_of_string (snd c))
  | TQualified lid ->
      let generic_params =
        if Idents.LidSet.mem lid env.pointer_holding_structs && Option.is_some config.lifetime then
          (* We are within a type declaration *)
          [ MiniRust.Lifetime (Option.get config.lifetime) ]
        else
          []
      in
      begin try
        Name (lookup_type env lid, generic_params)
      with Not_found ->
        Name (translate_unknown_lid lid, generic_params)
      end
  | TArrow _ ->
      let t, ts = Helpers.flatten_arrow t in
      let ts = match ts with [ TUnit ] -> [] | _ -> ts in
      Function (0, List.map (translate_type_with_config env config) ts, translate_type_with_config env config t)
  | TApp _ -> failwith "TODO: TApp"
  | TBound i -> Bound i
  | TTuple _ -> failwith "TODO: TTuple"
  | TAnonymous _ -> failwith "unexpected: we don't compile data types going to Rust"
  | TCgArray _ -> failwith "Impossible: TCgArray"
  | TCgApp _ -> failwith "Impossible: TCgApp"
  | TPoly _ -> failwith "Impossible: TPoly"

let translate_type env = translate_type_with_config env default_config


(* Expressions *)

(* Allocate a target Rust name for a definition named `lid` pertaining to file
   (i.e. future rust module) `prefix`.

   We do something super simple: we only retain the last component of `lid` and
   prefix it with the current namespace. This ensures that at Rust
   pretty-printing time, all the definitions in module m have their fully
   qualified names starting with m (and ending up with a single path component).

   As a further refinement, we at least make sure that the function is injective. The
   pretty-printing phase will take care of dealing with lexical conventions and the like (e.g. the
   fact that we oftentimes have single quotes in names but that's not ok in Rust -- not our problem
   here). *)
let translate_lid env lid =
  let rec translate_lid last i =
    let name = env.prefix @ [ last ^ string_of_int i ] in
    if NameSet.mem name env.global_scope then
      translate_lid last (i + 1)
    else
      allocate name
  and allocate name =
    { env with global_scope = NameSet.add name env.global_scope }, name
  in
  let name = env.prefix @ [ snd lid ] in
  if NameSet.mem name env.global_scope then
    translate_lid (snd lid) 0
  else
    allocate name


(* Trying to compile a *reference* to variable, who originates from a split of `v_base`, and whose
   original path in the tree is `path`. *)
let lookup_split (env: env) (v_base: MiniRust.db_index) (path: Splits.root_or_path): MiniRust.expr =
  if Options.debug "rs-splits" then
    KPrint.bprintf "looking up from base = %d path %s\n" v_base (Splits.show_root_or_path path);
  let rec find ofs bs =
    match bs with
    | (_, info) :: bs ->
        (* KPrint.bprintf "looking for %d\n" (v_base - ofs - 1); *)
        begin match info.Splits.path with
        | Some (v_base', path') when v_base' = v_base - ofs - 1 ->
            begin match Splits.accessible_via path path' with
            | Some pe ->
                MiniRust.(Field (Var ofs, Splits.string_of_path_elem pe, None))
            | None ->
                find (ofs + 1) bs
            end
        | _ ->
            find (ofs + 1) bs
        end
    | [] ->
        failwith "unexpected: path not found"
  in
  find 0 env.vars


let field_type env (e: Ast.expr) f =
  let t_lid = Helpers.assert_tlid e.typ in
  let struct_fields = LidMap.find t_lid env.struct_fields in
  (List.find (fun (sf: MiniRust.struct_field) -> sf.name = f) struct_fields).typ

(* Translate an expression, and take the annotated original type to be the
   expected type. *)
let rec translate_expr (env: env) (e: Ast.expr): env * MiniRust.expr =
  (* KPrint.bprintf "translate_expr: %a : %a\n" PrintAst.Ops.pexpr e PrintAst.Ops.ptyp e.typ; *)
  translate_expr_with_type env e (translate_type env e.typ)

and translate_expr_list (env: env) (es: Ast.expr list) : env * MiniRust.expr list =
  List.fold_left (fun (env, acc) e -> let env, e = translate_expr env e in env, acc @ [e]) (env, []) es

and translate_array (env: env) is_toplevel (init: Ast.expr): env * MiniRust.expr * MiniRust.typ =
  let to_array = function
    | Common.Stack -> true
    | Eternal -> is_toplevel
    | Heap -> false
  in

  match init.node with
  | EBufCreate (lifetime, e_init, len) ->
      let t = translate_type env (Helpers.assert_tbuf_or_tarray init.typ) in
      let env, len = translate_expr_with_type env len (Constant SizeT) in
      let env, e_init = translate_expr env e_init in
      let e_init = MiniRust.Repeat (e_init, len) in
      if to_array lifetime && H.is_const len then
        env, Array e_init, Array (t, H.assert_const len)
      else
        MiniRust.(env, box_new e_init, box (Slice t))
  | EBufCreateL (lifetime, es) ->
      let t = translate_type env (Helpers.assert_tbuf_or_tarray init.typ) in
      let l = List.length es in
      let env, es = translate_expr_list env es in
      let e_init = MiniRust.List es in
      if to_array lifetime then
        env, Array e_init, Array (t, l)
      else
        MiniRust.(env, box_new e_init, box (Slice t))
  | _ ->
      Warn.fatal_error "unexpected: non-bufcreate expression, got %a" PrintAst.Ops.pexpr init

(* However, generally, we will have a type provided by the context that may
   necessitate the insertion of conversions *)
and translate_expr_with_type (env: env) (e: Ast.expr) (t_ret: MiniRust.typ): env * MiniRust.expr =
  let erase_lifetime_info = (object(self)
    inherit [_] MiniRust.DeBruijn.map
    method! visit_Ref env _ bk t = Ref (None, bk, self#visit_typ env t)
    method! visit_tname _ n _ = Name (n, [])
  end)#visit_typ ()
  in

  (* KPrint.bprintf "translate_expr_with_type: %a @@ %a\n" PrintMiniRust.ptyp t_ret PrintAst.Ops.pexpr e; *)
  let possibly_convert (x: MiniRust.expr) t: MiniRust.expr =
    (* KPrint.bprintf "possibly_convert: %a: %a <: %a\n" *)
    (*   PrintMiniRust.pexpr x *)
    (*   PrintMiniRust.ptyp t *)
    (*   PrintMiniRust.ptyp t_ret; *)
    begin match x, t, t_ret with
    | _, (MiniRust.Vec _ | Array _), Ref (_, k, Slice _) ->
        Borrow (k, x)
    | Constant (w, x), Constant UInt32, Constant SizeT ->
        assert (w = Constant.UInt32);
        Constant (SizeT, x)
    | _, Constant UInt32, Constant SizeT ->
        As (x, Constant SizeT)
    | _, Function (_, ts, t), Function (_, ts', t') when ts = ts' && t = t' ->
        (* The type annotations coming from Ast do not feature polymorphic binders in types, but we
           do retain them in our Function type -- so we need to relax the comparison here *)
        x
    (* More conversions due to box-ing types. *)
    | _, App (Name (["Box"], _), [Slice _]), Ref (_, k, Slice _) ->
        Borrow (k, Deref x)
    | _, Ref (_, _, Slice _), App (Name (["Box"], _), [Slice _]) ->
        MethodCall (Borrow (Shared, Deref x), ["into"], [])
    (* | _, Ref (_, Shared, Slice _), App (Name (["Box"], _), [Slice _]) -> *)
    (*     MethodCall (x, ["into"], []) *)
    | _, Vec _, App (Name (["Box"], _), [Slice _]) ->
        MethodCall (MethodCall (x, ["try_into"], []), ["unwrap"], [])

    (* More conversions due to vec-ing types *)
    | _, Ref (_, _, Slice _), Vec _ ->
        MethodCall (x, ["to_vec"], [])
    | _, Array _, Vec _ ->
        Call (Name ["Vec"; "from"], [], [x])

    | _, Name (n, _), Name (n', _) when n = n' ->
        x
    | _, Ref (_, b, t), Ref (_, b', t') when b = b' && t = t' ->
        (* TODO: if field types are annotated with lifetimes, then we get a
           comparison where one side has a lifetime and the other doesn't -- we
           should probably run the arguments to this function through a
           strip_lifetimes function or something. *)
        x

    (* More conversions due to borrowing structs with pointers *)
    | _, Ref (_, _, t), t' when t = t' ->
      Deref x

    | Borrow (k, e) , Ref (_, _, t), Ref (_, _, Slice t') when t = t' ->
        Borrow (k, Array (List [ e ]))

    | _ ->
        (* If we reach this case, we perform one last try by erasing the lifetime
           information in both terms. This is useful to handle, e.g., implicit lifetime
           annotations or annotations up to alpha-conversion.
           Note, this is sound as lifetime mismatches will be caught by the Rust compiler *)
        if erase_lifetime_info t = erase_lifetime_info t_ret then
          x
        else
          Warn.failwith "type mismatch;\n  e=%a\n  t=%a\n  t_ret=%a\n  x=%a"
            PrintAst.Ops.pexpr e
            PrintMiniRust.ptyp t PrintMiniRust.ptyp t_ret
            PrintMiniRust.pexpr x;
    end
  in

  match e.node with
  | EOpen _ ->
      failwith "unexpected: EOpen"
  | EBound v ->
      if Options.debug "rs-splits" then begin
        KPrint.bprintf "Translating: %a\n" PrintAst.Ops.pexpr e;
        debug env
      end;

      let ({ MiniRust.typ; _ }: MiniRust.binding), info = lookup env v in
      let e =
        begin match info.path with
        | None -> possibly_convert (Var v) typ
        | Some (v_base, p) -> lookup_split env (v_base + v + 1) (Path p)
        end
      in

      (* Reset the tree for variable v, as accessing it invalidates previous
         splits on it.
         TODO: Should probably do this recursively *)
      let env = { env with vars =
        List.mapi (fun i (b, info) ->
          b, if i = v then {info with Splits.tree = Splits.Leaf } else info
        ) env.vars
      } in

      env, e

  | EOp (o, _) ->
      env, Operator o
  | EQualified lid ->
      begin try
        let name, t = lookup_decl env lid in
        env, possibly_convert (Name name) t
      with Not_found ->
        (* External -- TODO: make sure external definitions are properly added
           to the scope *)
        env, Name (translate_unknown_lid lid)
      end
  | EConstant c ->
      env, possibly_convert (Constant c) (Constant (fst c))
  | EUnit ->
      env, Unit
  | EBool b ->
      env, Constant (Bool, string_of_bool b)
  | EString s ->
      env, ConstantString s
  | EAny ->
      failwith "unexpected: [expr] no casts in Low* -> Rust"
  | EAbort (_, s) ->
      env, Panic (Stdlib.Option.value ~default:"" s)
  | EIgnore _ ->
      failwith "unexpected: EIgnore"
  | EApp ({ node = EOp (o, _); _ }, es) when H.is_wrapping_operator o ->
      let w = Helpers.assert_tint (List.hd es).typ in
      let env, es = translate_expr_list env es in
      env, possibly_convert (MethodCall (List.hd es, [ H.wrapping_operator o ], List.tl es)) (Constant w)

  | EApp ({ node = EQualified ([ "LowStar"; "BufferOps" ], s); _ }, e1 :: _) when KString.starts_with s "op_Bang_Star__" ->
      let env, e1 = translate_expr env e1 in
      (* env, Deref e1 *)
      env, Index (e1, MiniRust.zero_usize)

  | EApp ({ node = EQualified ([ "LowStar"; "BufferOps" ], s); _ }, e1 :: e2 :: _ ) when KString.starts_with s "op_Star_Equals__" ->
      let env, e1 = translate_expr env e1 in
      let t2 = translate_type env e2.typ in
      let env, e2 = translate_expr env e2 in
      env, Assign (Index (e1, MiniRust.zero_usize), e2, t2)

  | EApp ({ node = ETApp (e, cgs, cgs', ts); _ }, es) ->
      assert (cgs @ cgs' = []);
      let es =
        match es with
        | [ { typ = TUnit; node } ] -> assert (node = EUnit); []
        | _ -> es
      in
      let env, e = translate_expr env e in
      let ts = List.map (translate_type env) ts in
      let env, es = translate_expr_list env es in
      env, Call (e, ts, es)

  | EApp ({ node = EPolyComp (op, TBuf _); _ }, ([ { node = EBufNull; _ }; _ ] | [ _; { node = EBufNull; _ }])) ->
      (* No null-checks in Rust -- function will panic. *)
      begin match op with
      | PEq -> env, Constant (Bool, "false") (* nothing is ever null *)
      | PNeq ->  env, Constant (Bool, "true") (* everything is always non-null *)
      end

  | EApp (e0, es) ->
      let es =
        match es with
        | [ { typ = TUnit; node } ] -> assert (node = EUnit); []
        | _ -> es
      in
      let env, e0 = translate_expr env e0 in
      let env, es = translate_expr_list env es in
      env, possibly_convert (Call (e0, [], es)) (translate_type env e.typ)

  | ETApp (_, _, _, _) ->
      failwith "TODO: ETApp"

  | EPolyComp (op, _t) ->
      (* All that is left here is enumerations, which *do* derive eq. *)
      begin match op with
      | PEq -> env, Operator Eq
      | PNeq -> env, Operator Neq
      end
      (* failwith (KPrint.bsprintf "unexpected: EPolyComp at type %a" PrintAst.Ops.ptyp t) *)

  | ELet (b, ({ node = EBufSub ({ node = EBound v_base; _ } as e_base, e_ofs); _ } as e1), e2) ->
      (* Keep initial environment to return after translation *)
      let env0 = env in
      if Options.debug "rs-splits" then begin
        KPrint.bprintf "Translating: let %a = %a\n" PrintAst.Ops.pbind b PrintAst.Ops.pexpr e1;
        debug env
      end;

      let l = List.length env.vars in

      let env, e_ofs' = translate_expr env e_ofs in
      let index = Splits.index_of_expr l e_ofs' (translate_type env e_ofs.typ) in
      (* We're splitting a variable x_base. *)
      let _, info_base = lookup env v_base in
      (* At the end of `path` is the variable we want to split. *)
      let info_base, path, index = Splits.split env.location l info_base index in

      let env, e_nearest =
        if path = [] then
          translate_expr env e_base
        else
          let path, path_elem = KList.split_at_last path in
          let rec find ofs bs =
            match bs with
            | (_, info) :: bs ->
                (* KPrint.bprintf "[ELet] looking for %d\n" (v_base - ofs - 1); *)
                begin match info.Splits.path with
                | Some (v_base', path') when v_base' = v_base - ofs - 1 && path' = path ->
                    MiniRust.(Var ofs)
                | _ ->
                    find (ofs + 1) bs
                end
            | [] ->
                failwith "[ELet] unexpected: path not found"
          in
          env, MiniRust.(Field (find 0 env.vars, Splits.string_of_path_elem path_elem, None))
      in

      let split_at = "split_at" in
      let e1 = MiniRust.MethodCall (e_nearest , [split_at], [ index ]) in
      let t = translate_type env b.typ in
      let binding : MiniRust.binding * Splits.info =
        { name = b.node.name; typ = Tuple [ t; t ]; mut = false },
        { tree = Leaf; path = Some (v_base, path) }
      in

      (* Now, update a few things in the environment. *)
      let env = { env with vars =
        List.mapi (fun i (b, info) ->
          b, if i = v_base then info_base else info
        ) env.vars
      } in
      let env = push_with_info env binding in

      env0, Let (fst binding, e1, snd (translate_expr_with_type env e2 t_ret))

  | ELet (b, ({ node = EBufCreate _ | EBufCreateL _; _ } as init), e2) ->
      (* Keep initial environment to return after translation *)
      let env0 = env in

      let env, e1, t = translate_array env false init in
      (* KPrint.bprintf "Let %s: %a\n" b.node.name PrintMiniRust.ptyp t; *)
      let binding: MiniRust.binding = { name = b.node.name; typ = t; mut = false } in
      let env = push env binding in
      env0, Let (binding, e1, snd (translate_expr_with_type env e2 t_ret))

  | ELet (b, e1, e2) ->
      (* Keep initial environment to return after translation *)
      let env0 = env in

      let env, e1 = translate_expr env e1 in
      let t = translate_type env b.typ in
      let is_owned_struct =
        match b.typ with
        | TQualified lid when Idents.LidSet.mem lid env.heap_structs || Idents.LidSet.mem lid env.pointer_holding_structs -> true
        | _ -> false
      in
      (* TODO how does this play out with the new "translate as non-mut by
         default" strategy? *)
      let mut = b.node.mut || is_owned_struct in
      (* Here, the idea is to detect forbidden move-outs that are certain to result in a compilation
         error. Typically, selecting a field, dereferencing an array, etc. when the underlying type
         contains pointers means that the let-binding will be a move-out (i.e. moving out PART of an
         object), which Rust forbids. Note that if t is a pointer type, this is fine, since we
         compiler our pointer types as borrows, which means there is no move-out, only a borrow. But
         if t is a struct type which contains pointers (hence, does not implement the copy trait),
         this is certain to fail. In that case, we instead borrow the struct. Note that structs
         cannot be mutated in place in Low*, so it's ok to borrow instead of copy. *)
      let e1, t = match e1 with
        | (Field _ | Index _) when is_owned_struct ->
            MiniRust.(Borrow (Shared, e1), Ref (None, Shared, t))
        | _ ->
            e1, t
      in
      let binding : MiniRust.binding = { name = b.node.name; typ = t; mut } in
      let env = push env binding in
      env0, Let (binding, e1, snd (translate_expr_with_type env e2 t_ret))

  | EFun _ ->
      failwith "unexpected: EFun"

  | EIfThenElse (e1, e2, e3) ->
      let env, e1 = translate_expr env e1 in
      let env, e2 = translate_expr_with_type env e2 t_ret in
      let env, e3 = if e3.node = EUnit then env, None else let env, e3 = translate_expr_with_type env e3 t_ret in env, Some e3 in
      env, IfThenElse (e1, e2, e3)
  | ESequence _ ->
      failwith "unexpected: ESequence"
  | EAssign (e1, e2) ->
      let lvalue_type = match e1.node with
        | EField (e, f) -> field_type env e f
        | _ -> translate_type env e1.typ
      in
      let env, e1 = translate_expr_with_type env e1 lvalue_type in
      let env, e2 = translate_expr_with_type env e2 lvalue_type in
      env, Assign (e1, e2, lvalue_type)
  | EBufCreate _ ->
      failwith "unexpected: EBufCreate"
  | EBufCreateL _ ->
      failwith "unexpected: EBufCreateL"
  | EBufRead (e1, e2) ->
      let env, e1 = translate_expr env e1 in
      let env, e2 = translate_expr_with_type env e2 (Constant SizeT) in
      env, Index (e1, e2)
  | EBufWrite (e1, e2, e3) ->
      let env, e1 = translate_expr env e1 in
      let env, e2 = translate_expr_with_type env e2 (Constant SizeT) in
      let t3 = translate_type env e3.typ in
      let env, e3 = translate_expr env e3 in
      env, Assign (Index (e1, e2), e3, t3)
  | EBufSub (e1, e2) ->
      (* This is a fallback for the analysis above. Happens if, for instance, the pointer arithmetic
         appears in subexpression position (like, function call), in which case there's a chance
         this might still work! *)
      let env, e1 = translate_expr env e1 in
      let env, e2 = translate_expr_with_type env e2 (Constant SizeT) in
      env, Borrow (Shared, Index (e1, Range (Some e2, None, false)))
  | EBufDiff _ ->
      failwith "unexpected: EBufDiff"
  (* Silly pattern in Low*: for historical reasons, the blit operations takes a
     monotonic buffer (with any preorder) as its `src` argument. Since const pointers are an
     abstract type, there is an explicit coercion *to mutable* to pass a const pointer as the source
     of a bufblit operation. This is backwards, and should be fixed with an alternative `blit`
     function in the ConstBuffer module (or in the BufferOps module). *)
  | EBufBlit ({ node = ECast ({ typ = TBuf (_, true); _ } as src, TBuf (_, false)); _ }, src_index, dst, dst_index, len)
  | EBufBlit (src, src_index, dst, dst_index, len) ->
      let env, src = translate_expr env src in
      let env, src_index = translate_expr_with_type env src_index (Constant SizeT) in
      let env, dst = translate_expr env dst in
      let env, dst_index = translate_expr_with_type env dst_index (Constant SizeT) in
      let env, len = translate_expr_with_type env len (Constant SizeT) in
      env, MethodCall (
        Index (dst, H.range_with_len dst_index len),
        [ "copy_from_slice" ],
        [ Borrow (Shared, Index (src, H.range_with_len src_index len)) ])
  | EBufFill (dst, elt, len) ->
      (* let t = translate_type env elt.typ in *)
      let env, dst = translate_expr env dst in
      let env, elt = translate_expr env elt in
      let env, len = translate_expr_with_type env len (Constant SizeT) in
      if H.is_const len then
        env, MethodCall (
          Index (dst, H.range_with_len (Constant (SizeT, "0")) len),
          [ "copy_from_slice" ],
          [ Borrow (Shared, Array (Repeat (elt, len))) ])
      else
        env, MethodCall (
          Index (dst, H.range_with_len (Constant (SizeT, "0")) len),
          [ "copy_from_slice" ],
          [ Borrow (Shared, MiniRust.(box_new (Repeat (elt, len)))) ])
  | EBufFree _ ->
      (* Rather than error out, we do nothing, as some functions may allocate then free. *)
      env, Unit
  | EBufNull ->
      env, possibly_convert (Borrow (Shared, Array (List []))) (translate_type env e.typ)
  | EPushFrame ->
      failwith "unexpected: EPushFrame"
  | EPopFrame ->
      failwith "unexpected: EPopFrame"

  | ETuple _ ->
      failwith "TODO: ETuple"
  | EMatch _ ->
      failwith "TODO: EMatch"
  | ECons _ ->
      failwith "TODO: ECons"

  | ESwitch (scrut, patexprs) ->
      let env, scrut_ = translate_expr env scrut in
      let patexprs = List.map (fun (p, e) ->
        let p =
          match p with
          | Ast.SConstant c ->
              MiniRust.Literal c
          | SEnum lid ->
              let name = lookup_type env (Helpers.assert_tlid scrut.Ast.typ) in
              StructP (name @ [ snd lid ])
          | SWild ->
              Wildcard
        in
        p, snd (translate_expr env e)
      ) patexprs in
      (* Meh. We can't detect complete pattern matches, but we can't detect
         incomplete ones either. Unreachable wildcards are a warning, incomplete
         pattern matches are an error. *)
      let patexprs =
        if not (List.exists (fun (p, _) -> p = MiniRust.Wildcard) patexprs) then
          patexprs @ [ Wildcard, Panic "Precondition of the function most likely violated" ]
        else
          patexprs
      in
      env, Match (scrut_, patexprs)

  | EEnum lid ->
      let name = lookup_type env (Helpers.assert_tlid e.typ) in
      env, Name (name @ [ snd lid ])

  | EFlat fields ->
      let t_lid = Helpers.assert_tlid e.typ in
      let struct_fields = LidMap.find t_lid env.struct_fields in
      let env, fields = List.fold_left (fun (env, fields) (f, e) ->
        let f = Option.get f in
        let ret_t = (List.find (fun (sf: MiniRust.struct_field) -> sf.name = f) struct_fields).typ in
        let env, e = translate_expr_with_type env e ret_t in
        env, (f, e) :: fields
      ) (env, []) fields in
      env, Struct (lookup_type env t_lid, List.rev fields)

  | EField (e, f) ->
      let env, e_ = translate_expr env e in
      let t = translate_type env e.typ in
      env, possibly_convert (Field (e_, f, Some t)) (field_type env e f)

  | EBreak ->
      failwith "TODO: EBreak"
  | EContinue ->
      failwith "TODO: EContinue"
  | EReturn _ ->
      failwith "TODO: EReturn"
  | EWhile _ ->
      failwith "TODO: EWhile"

  (* The introduction of the unroll_loops macro requires a "fake" binder
     for the iterated value, which messes up with variable substitutions
     mutability inference. We instead perform it in RustMacroize, after
     all substitutions are done. *)
  | EFor (b, e_start, e_test, e_incr, e_body) ->
      (* Keep initial environment to return after translation *)
      let env0 = env in

      (* b is in scope for e_test, e_incr, e_body! *)
      let e_end = match e_test.node, e_incr.node with
        (* If we have `i < e_end; i := i + 1`, then this is a range-loop and we can
           lift `e_end` by 1. *)
        | EApp ({ node = EOp (Lt, _); _ }, [ { node = EBound 0; _ }; e_end ]),
        EAssign ({ node = EBound 0; _ },
          { node = EApp ({ node = EOp ((Add | AddW), _); _ }, [
            { node = EBound 0; _ };
            { node = EConstant (_, "1"); _ } ]); _ }) ->
              (* Assuming that b does not occur in e_end *)
              DeBruijn.subst Helpers.eunit 0 e_end
        | _ ->
            Warn.failwith "Unsupported loop:\n e_test=%a\n e_incr=%a\n"
              PrintAst.Ops.pexpr e_test
              PrintAst.Ops.pexpr e_incr
      in
      (* The loop index is unused if it has at most three uses; in that case,
         all of those are in `i < e_end i := i + 1`, and they all go away since
         this loop compiles to `i in e_start..e_end`, effectively marking this
         variable unused. *)
      let unused = snd !(b.node.mark) = AtMost 3 in
      (* We do an ad-hoc thing since this didn't go through lowstar.ignore
         insertion. Rust uses the OCaml convention (which I recall I did suggest
         to Graydon back in 2010). *)
      let unused = if unused then "_" else "" in
      let binding: MiniRust.binding = { name = unused ^ b.node.name; typ = translate_type env b.typ; mut = false } in
      let env, e_start = translate_expr env e_start in
      let env, e_end = translate_expr env e_end in
      let _, e_body = translate_expr (push env binding) e_body in
      env0, For (binding, Range (Some e_start, Some e_end, false), e_body)
  | ECast (e, t) ->
      let env, e = translate_expr env e in
      env, As (e, translate_type env t)
  | EComment _ ->
      failwith "TODO: EComment"
  | EStandaloneComment _ ->
      failwith "TODO: EStandaloneComment"
  | EAddrOf _e1 ->
      (* This should not be generated by krml on the basis that the
         compilation scheme below (left for reference) is incorrect, in
        combination with possibly_convert -- it compiles &x to &[x] where a copy
        of x is inserted into a slice, meaning further modifications affect a copy
        of x, not x itself *)
      failwith "Unexpected: EAddrOf"
      (* PREVIOUSLY: *)
      (* let env, e1_ = translate_expr env e1 in *)
      (* env, possibly_convert (Borrow (Mut, e1_)) (Ref (None, Mut, translate_type env e1.typ)) *)
      (* POSSIBLE FIX (if we care): insert slice::from_ref, since the expected
         Rust type for this is a slice (and maybe ditch possibly_convert) *)

let make_poly (t: MiniRust.typ) n: MiniRust.typ =
  match t with
  | Function (n', ts, t) ->
      assert (n' = 0);
      Function (n, ts, t)
  | _ ->
      (* Constants aren't supposed to be polymorphic *)
      assert (n = 0);
      t

let is_handled_primitively = function
  | [ "LowStar"; "BufferOps" ], s ->
      KString.starts_with s "op_Bang_Star__" ||
      KString.starts_with s "op_Star_Equals__"
  | _ ->
      false

(* In Rust, like in C, all the declarations from the current module are in
 * scope immediately. This requires us to duplicate a little bit of work. *)
let bind_decl env (d: Ast.decl): env =
  match d with
  | DFunction (_, _, _, _, _, lid, _, _) when is_handled_primitively lid ->
      env
  | DFunction (_cc, _flags, _n_cgs, type_parameters, t, lid, args, _body) ->
      let env, name = translate_lid env lid in
      let args =
        if List.length args = 1 && (List.hd args).Ast.typ = TUnit then
          []
        else
          args
      in
      let parameters = List.map (fun (b: Ast.binder) ->
        translate_type env b.typ
      ) args in
      let is_likely_heap_allocation =
        KString.exists (snd lid) "new" ||
        KString.exists (snd lid) "malloc"
      in
      let return_type =
        let box = match t with
        | TBuf (TQualified lid, _) when Idents.LidSet.mem lid env.heap_structs ->
            true
        | TBuf _ when is_likely_heap_allocation ->
            true
        | _ ->
            false
        in
        translate_type_with_config env { default_config with box } t
      in
      push_decl env lid (name, Function (type_parameters, parameters, return_type))

  | DGlobal (_flags, lid, _, t, e) ->
      let typ = match e.node with
        | EBufCreate _ | EBufCreateL _ ->
            (* TODO: split out the type computation *)
            let _, _, typ = translate_array env true e in
            typ
        | _ ->
            translate_type env t
      in
      let env, name = translate_lid env lid in
      push_decl env lid (name, typ)

  | DExternal (_, _, _, type_parameters, lid, t, _param_names) ->
      let name = translate_unknown_lid lid in
      push_decl env lid (name, make_poly (translate_type env t) type_parameters)

  | DType (lid, _flags, _, _, decl) ->
      let env, name = translate_lid env lid in
      let env = push_type env lid name in
      match decl with
      | Flat fields ->
          (* These sets are mutually exclusive, so we don't box *and* introduce a
             lifetime at the same time *)
          let box = Idents.LidSet.mem lid env.heap_structs in
          KPrint.bprintf "%a: lifetime=%b\n" PrintAst.Ops.plid lid (Idents.LidSet.mem lid env.pointer_holding_structs);
          let lifetime =
            if Idents.LidSet.mem lid env.pointer_holding_structs then
              Some (MiniRust.Label "a")
            else
              None
          in
          let fields = List.map (fun (f, (t, _m)) ->
            let f = Option.get f in
            { MiniRust.name = f; visibility = Some Pub; typ = translate_type_with_config env { box; lifetime } t }
          ) fields in
          { env with struct_fields = LidMap.add lid fields env.struct_fields }
      | _ ->
          env

let translate_meta flags =
  let comments = List.filter_map (function Common.Comment c -> Some c | _ -> None) flags in
  let comments = List.filter ((<>) "") comments in
  let visibility =
    if List.mem Common.Private flags then
      None
    else if List.mem Common.Internal flags then
      Some MiniRust.PubCrate
    else
      Some Pub
  in
  {
    MiniRust.visibility;
    comment = String.concat "\n" comments;
  }

let translate_decl env (d: Ast.decl): MiniRust.decl option =
  let env = locate env (Ast.lid_of_decl d) in
  match d with
  | DFunction (_, _, _, _, _, lid, _, _) when is_handled_primitively lid ->
      None
  | DFunction (_cc, flags, n_cgs, type_parameters, _t, lid, args, body) ->
      assert (type_parameters = 0 && n_cgs = 0);
      if Options.debug "rs" then
        KPrint.bprintf "Ast.DFunction (%a)\n" PrintAst.Ops.plid lid;
      let name, parameters, return_type =
        match lookup_decl env lid with
        | name, Function (_, parameters, return_type) -> name, parameters, return_type
        | _ -> failwith "impossible"
      in
      let body, args = if parameters = [] then DeBruijn.subst Helpers.eunit 0 body, [] else body, args in
      let parameters = List.map2 (fun typ a -> { MiniRust.mut = false; name = a.Ast.node.Ast.name; typ }) parameters args in
      let env = List.fold_left push env parameters in
      let _, body = translate_expr_with_type env body return_type in
      let meta = translate_meta flags in
      let inline = List.mem Common.Inline flags in
      Some (MiniRust.Function { type_parameters; parameters; return_type; body; name; meta; inline })

  | DGlobal (flags, lid, _, _t, e) ->
      let name, typ = lookup_decl env lid in
      if Options.debug "rs" then
        KPrint.bprintf "Ast.DGlobal (%a: %s)\n" PrintAst.Ops.plid lid (MiniRust.show_typ typ);
      let body = match e.node with
        | EBufCreate _ | EBufCreateL _ ->
            (* TODO: split out body computation *)
            let _, body, _ = translate_array env true e in body
        | _ ->
            snd (translate_expr env e)
      in
      let meta = translate_meta flags in
      Some (MiniRust.Constant { name; typ; body; meta })

  | DExternal _ ->
      None

  | DType (lid, flags, _, _, decl) ->
      (* creative naming for the lifetime *)
      let name = lookup_type env lid in
      let meta = translate_meta flags in
      match decl with
      | Flat _ ->
          let lifetime =
            if Idents.LidSet.mem lid env.pointer_holding_structs then
              Some (MiniRust.Label "a")
            else
              None
          in
          let generic_params = match lifetime with Some l -> [ MiniRust.Lifetime l ] | None -> [] in
          let fields = LidMap.find lid env.struct_fields in
          Some (Struct { name; meta; fields; generic_params })
      | Enum idents ->
          (* No need to do name binding here since there are entirely resolved via the type name. *)
          let items = List.map (fun i -> [ snd i ], None) idents in
          Some (Enumeration { name; meta; items; derives = [ PartialEq; Clone; Copy ] })
      | Abbrev t ->
          let has_inner_pointer = (object
            inherit [_] Ast.reduce
            method zero = false
            method plus = (||)
            method! visit_TBuf _ _ _ = true
            method! visit_TQualified _ lid = Idents.LidSet.mem lid env.pointer_holding_structs
          end)#visit_typ () t in
          let lifetime, generic_params =
            if has_inner_pointer then
              Some (MiniRust.Label "a"), [ MiniRust.Lifetime (Label "a") ]
            else
              None, []
          in
          let t = translate_type_with_config env { default_config with lifetime } t in
          Some (Alias { name; meta; body = t; generic_params })
      | Variant _
      | Union _
      | Forward _ ->
          Warn.failwith "TODO: Ast.DType (%a)\n" PrintAst.Ops.plid lid

let identify_path_components_rev filename =
  let components = ref [] in
  let is_uppercase c = 'A' <= c && c <= 'Z' in
  let start = ref 0 in
  for i = 0 to String.length filename - 2 do
    if filename.[i] = '_' && is_uppercase filename.[i+1] then begin
      components := String.sub filename !start (i - !start) :: !components;
      start := i + 1
    end
  done;
  if !start <> String.length filename - 1 then
    components := String.sub filename !start (String.length filename - !start) :: !components;
  !components

let compute_struct_info files =
  (* A table from lid to fields, for all the structs in the program. *)
  let struct_map = List.fold_left (fun acc (_, decls) ->
    List.fold_left (fun acc decl ->
      match decl with
      | Ast.DType (lid, _, _, _, Flat fields) ->
          Idents.LidMap.add lid fields acc
      | _ ->
          acc
    ) acc decls
  ) Idents.LidMap.empty files in

  (* Base case: types that appear in return position. *)
  let returned = (object
    inherit [_] Ast.reduce
    method zero = Idents.LidSet.empty
    method plus = Idents.LidSet.union
    method! visit_DFunction _ _ _ _ _ ret_t _ _ _ =
      match ret_t with
      | TQualified lid -> Idents.LidSet.singleton lid
      | _ -> Idents.LidSet.empty
  end)#visit_files () files in

  (* Transitive closure: all the types that appear as part of a returned type. *)
  let returned =
    let h = Hashtbl.create 41 in
    let rec visit_fields fields =
      (object
        inherit [_] Ast.iter as super
        method! visit_TQualified _ lid = visit lid
        method! visit_TApp _ lid ts = visit lid; super#visit_TApp () lid ts
      end)#visit_fields_t_opt () fields
    and visit lid =
      if not (Hashtbl.mem h lid) then begin
        Hashtbl.add h lid ();
        match Idents.LidMap.find_opt lid struct_map with
        | None ->
            ()
        | Some fields -> visit_fields fields
      end
    in
    Idents.LidSet.iter visit returned;
    Idents.LidSet.of_seq (Hashtbl.to_seq_keys h)
  in

  let struct_fixpoint base_case =
    let module F = Fix.Fix.ForOrderedType(struct
      type t = Ast.lident
      let compare = Stdlib.compare
    end)(struct
      type property = bool
      let bottom = false
      let equal = (=)
      let is_maximal x = x
    end) in

    let equations lid valuation =
      if not (Idents.LidMap.mem lid struct_map) then
        false
      else
        base_case lid &&
        let fields = Idents.LidMap.find lid struct_map in
        let recursively_contains_pointers = (object(self)
            inherit [_] Ast.reduce as super
            method zero = false
            method plus = (||)
            method! visit_TQualified _ lid =
              valuation lid
            method! visit_TApp env lid ts =
              self#plus (valuation lid) (super#visit_TApp env lid ts)
          end)#visit_fields_t_opt () fields
        in
        let directly_contains_pointers =
          List.exists (fun (_, (t, _)) -> match t with Ast.TBuf _ -> true | _ -> false) fields
        in
        directly_contains_pointers || recursively_contains_pointers
    in

    let valuation = F.lfp equations in

    Idents.LidMap.fold (fun lid _ acc ->
      if valuation lid then Idents.LidSet.add lid acc else acc
    ) struct_map Idents.LidSet.empty
  in

  (* The base case of the fixpoint is structs that are *not returned* and still contain
     pointers. We backpropagate starting from that. *)
  let with_inner_pointers = struct_fixpoint (fun lid -> not (Idents.LidSet.mem lid returned)) in
  (* This one eliminates structs that are in the returned-set but do not contain pointers. *)
  let returned = struct_fixpoint (fun lid -> Idents.LidSet.mem lid returned) in

  assert Idents.LidSet.(is_empty (inter with_inner_pointers returned));

  if Options.debug "rs-structs" then begin
    KPrint.bprintf "returned: %a\n\n" PrintAst.Ops.plids (Idents.LidSet.elements returned);
    KPrint.bprintf "with_inner_pointers: %a\n\n" PrintAst.Ops.plids (Idents.LidSet.elements with_inner_pointers);
  end;

  returned, with_inner_pointers

let translate_files files =
  let heap_structs, pointer_holding_structs = compute_struct_info files in
  if Options.debug "rs-structs" then begin
    KPrint.bprintf "The following types are understood to be heap-allocated:\n";
    List.iter (KPrint.bprintf "  %a\n" PrintAst.Ops.plid) (Idents.LidSet.elements heap_structs)
  end;

  let failures = ref 0 in
  let env, files = List.fold_left (fun (env, files) (f, decls) ->
    let prefix = List.map String.lowercase_ascii (identify_path_components_rev f) in
    let prefix = compress_prefix (List.rev prefix) in
    if Options.debug "rs" then
      KPrint.bprintf "Translating file %s\n" (String.concat "::" prefix);
    let total = List.length decls in
    let env = { env with prefix } in

    (* Step 1: bind all declarations and add them to the environment with their types *)
    let env = List.fold_left (fun env d ->
      try
        bind_decl env d
      with e ->
        (* We do not increase failures as this will be counted below. *)
        KPrint.bprintf "%sERROR translating type of %a: %s%s\n%s\n" Ansi.red
          PrintAst.Ops.plid (Ast.lid_of_decl d)
          (Printexc.to_string e) Ansi.reset
          (Printexc.get_backtrace ());
        env
    ) env decls in

    (* Step 2: translate all declarations themselves. If step 1 didn't succeed
       for some declaration, this will fail with Not_found via either
       lookup_decl or lookup_type *)
    let decls = List.map (fun d ->
      try
        translate_decl env d
      with e ->
        incr failures;
        KPrint.bprintf "%sERROR translating %a: %s%s\n%s\n" Ansi.red
          PrintAst.Ops.plid (Ast.lid_of_decl d)
          (Printexc.to_string e) Ansi.reset
          (Printexc.get_backtrace ());
        None
    ) decls in

    if Options.debug "rs" then
      KPrint.bprintf "... translated file %s (%d/%d)\n" (String.concat "::" prefix) (List.length decls) total;

    let decls = KList.filter_some decls in
    env, (prefix, decls) :: files
  ) (empty heap_structs pointer_holding_structs, []) files in

  if Options.debug "rs" then
    LidMap.iter (fun lid (name, _) ->
      KPrint.bprintf "%a --> %s\n" PrintAst.Ops.plid lid (PrintMiniRust.string_of_name name)
    ) env.decls;

  if !failures > 0 then
    KPrint.bprintf "%s%d total errors%s\n" Ansi.red !failures Ansi.reset;

  List.rev files

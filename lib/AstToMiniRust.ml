(* Low* to Rust backend *)

module LidMap = Idents.LidMap

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
    Option.must (wrapping_operator_opt o)

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

  let gte i1 i2 =
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
        KPrint.bprintf "WARN: cannot compare constant %d and %a + %d\n"
          i1 PrintMiniRust.pexpr (snd e2) i2;
        true
    | Add (e1, i1), Add (e2, i2) ->
        (* TODO: proper warning system *)
        KPrint.bprintf "WARN: Cannot compare %a@%d + %d and %a@%d + %d\n"
          PrintMiniRust.pexpr (snd e1) (fst e1) i1
          PrintMiniRust.pexpr (snd e2) (fst e2) i2;
        true

  let sub i1 i2 =
    match i1, i2 with
    | Constant i1, Constant i2 ->
        Constant (i1 - i2)
    | Add (e1, i1), Add (e2, i2) when term_eq e1 e2 ->
        Constant (i1 - i2)
    | Add (e1, i1), Constant i2 ->
        Add (e1, i1 - i2)
    | Constant i1, Add ((l2, e2), i2) ->
        KPrint.bprintf "WARN: Cannot subtract constant %d and %a + %d\n\
          assuming monotonically increasing indices, this may cause runtime failures\n"
          i1 PrintMiniRust.pexpr e2 i2;
        (* i1 - (e2 + i2) *)
        Add ((l2, H.sub (H.usize i1) (H.add e2 (H.usize i2))), 0)
    | Add (e1, i1), Add (e2, i2) ->
        let l, e1, e2 = equalize e1 e2 in
        KPrint.bprintf "WARN: Cannot subtract constant %a@%d + %d and %a@%d + %d\n\
          assuming monotonically increasing indices, this may cause runtime failures\n"
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
  let split l info index: info * path * MiniRust.expr =
    let rec split tree index ofs =
      match tree with
      | Leaf ->
          Node (index, Leaf, Leaf), [], ofs
      | Node (index', t1, t2) ->
          if gte index index' then
            let t2, path, ofs = split t2 index (sub index index') in
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

type env = {
  decls: (MiniRust.name * MiniRust.typ) LidMap.t;
  types: MiniRust.name LidMap.t;
  vars: (MiniRust.binding * Splits.info) list;
  prefix: string list;
}

let empty = { decls = LidMap.empty; types = LidMap.empty; vars = []; prefix = [] }

let push env b = { env with vars = (b, Splits.empty) :: env.vars }

let push_with_info env b = { env with vars = b :: env.vars }

let push_global env name t =
  assert (not (LidMap.mem name env.decls));
  { env with decls = LidMap.add name t env.decls }

let lookup env v = List.nth env.vars v

let lookup_decl env name =
  LidMap.find name env.decls

let lookup_type env name =
  LidMap.find name env.types

let debug env =
  List.iteri (fun i (b, info) ->
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

let borrow_kind_of_bool b: MiniRust.borrow_kind =
  if b (* const *) then
    Shared
  else
    Mut

let rec translate_type (env: env) (t: Ast.typ): MiniRust.typ =
  match t with
  | TInt w -> Constant w
  | TBool -> Constant Bool
  | TUnit -> Unit
  | TAny -> failwith "unexpected: [type] no casts in Low* -> Rust"
  | TBuf (t, b) -> Ref (borrow_kind_of_bool b, Slice (translate_type env t))
  | TArray (t, c) -> Array (translate_type env t, int_of_string (snd c))
  | TQualified lid ->
      begin try
        Name (lookup_type env lid)
      with Not_found ->
        Name (translate_unknown_lid lid)
      end
  | TArrow _ ->
      let t, ts = Helpers.flatten_arrow t in
      let ts = match ts with [ TUnit ] -> [] | _ -> ts in
      Function (0, List.map (translate_type env) ts, translate_type env t)
  | TApp _ -> failwith "TODO: TApp"
  | TBound i -> Bound i
  | TTuple _ -> failwith "TODO: TTuple"
  | TAnonymous _ -> failwith "unexpected: we don't compile data types going to Rust"
  | TBottom -> failwith "impossible: TBottom not eliminated"


(* Expressions *)

(* Allocate a target Rust name for a definition named `lid` pertaining to file
   (i.e. future rust module) `prefix`.

   We do something super simple: we only retain the last component of `lid` and
   prefix it with the current namespace. This ensures that at Rust
   pretty-printing time, all the definitions in module m have their fully
   qualified names starting with m (and ending up with a single path component).

   This leaves a lot of room for a better strategy, but this can happen later. *)
let translate_lid env lid =
  env.prefix @ [ snd lid ]


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
                MiniRust.(Field (Var ofs, Splits.string_of_path_elem pe))
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

(* Translate an expression, and take the annotated original type to be the
   expected type. *)
let rec translate_expr (env: env) (e: Ast.expr): MiniRust.expr =
  (* KPrint.bprintf "translate_expr: %a : %a\n" PrintAst.Ops.pexpr e PrintAst.Ops.ptyp e.typ; *)
  translate_expr_with_type env e (translate_type env e.typ)

and translate_array (env: env) is_toplevel (init: Ast.expr): MiniRust.expr * MiniRust.typ =
  let to_array = function
    | Common.Stack -> true
    | Eternal -> is_toplevel
    | Heap -> false
  in

  match init.node with
  | EBufCreate (lifetime, e_init, len) ->
      let t = translate_type env (Helpers.assert_tbuf_or_tarray init.typ) in
      let len = translate_expr_with_type env len (Constant SizeT) in
      let e_init = MiniRust.Repeat (translate_expr env e_init, len) in
      if to_array lifetime && H.is_const len then
        Array e_init, Array (t, H.assert_const len)
      else
        VecNew e_init, Vec t
  | EBufCreateL (lifetime, es) ->
      let t = translate_type env (Helpers.assert_tbuf_or_tarray init.typ) in
      let l = List.length es in
      let e_init = MiniRust.List (List.map (translate_expr env) es) in
      if to_array lifetime then
        Array e_init, Array (t, l)
      else
        VecNew e_init, Vec t
  | _ ->
      Warn.fatal_error "unexpected: non-bufcreate expression, got %a" PrintAst.Ops.pexpr init

(* However, generally, we will have a type provided by the context that may
   necessitate the insertion of conversions *)
and translate_expr_with_type (env: env) (e: Ast.expr) (t_ret: MiniRust.typ): MiniRust.expr =
  (* KPrint.bprintf "translate_expr_with_type: %a @@ %a\n" PrintMiniRust.ptyp t_ret PrintAst.Ops.pexpr e; *)
  let possibly_convert (x: MiniRust.expr) t: MiniRust.expr =
    begin match x, t, t_ret with
    | _, (MiniRust.Vec _ | Array _), Ref (k, Slice _) ->
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
    | _ ->
        if t = t_ret then
          x
        else
          Warn.failwith "type mismatch;\n  e=%a\n  t=%s\n  t_ret=%s\n  x=%s"
            PrintAst.Ops.pexpr e
            (MiniRust.show_typ t) (MiniRust.show_typ t_ret)
            (MiniRust.show_expr x)
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

      let { MiniRust.typ; _ }, info = lookup env v in
      if info.tree <> Leaf then
        match Splits.find_zero info.tree with
        | Some p -> lookup_split env v (Path p)
        | None -> lookup_split env v Root
      else
        begin match info.path with
        | None -> possibly_convert (Var v) typ
        | Some (v_base, p) -> lookup_split env (v_base + v + 1) (Path p)
        end

  | EOp (o, _) ->
      Operator o
  | EQualified lid ->
      begin try
        let name, t = lookup_decl env lid in
        possibly_convert (Name name) t
      with Not_found ->
        (* External -- TODO: make sure external definitions are properly added
           to the scope *)
        Name (translate_unknown_lid lid)
      end
  | EConstant c ->
      possibly_convert (Constant c) (Constant (fst c))
  | EUnit ->
      Unit
  | EBool b ->
      Constant (Bool, string_of_bool b)
  | EString s ->
      ConstantString s
  | EAny ->
      failwith "unexpected: [expr] no casts in Low* -> Rust"
  | EAbort (_, s) ->
      Panic (Stdlib.Option.value ~default:"" s)
  | EIgnore _ ->
      failwith "unexpected: EIgnore"
  | EApp ({ node = EOp (o, _); _ }, es) when H.is_wrapping_operator o ->
      let w = Helpers.assert_tint (List.hd es).typ in
      let es = List.map (translate_expr env) es in
      possibly_convert (MethodCall (List.hd es, [ H.wrapping_operator o ], List.tl es)) (Constant w)

  | EApp ({ node = EQualified ([ "LowStar"; "BufferOps" ], s); _ }, e1 :: _) when KString.starts_with s "op_Bang_Star__" ->
      Deref (translate_expr env e1)

  | EApp ({ node = EQualified ([ "LowStar"; "BufferOps" ], s); _ }, e1 :: e2 :: _ ) when KString.starts_with s "op_Star_Equals__" ->
      Assign (Deref (translate_expr env e1), translate_expr env e2)

  | EApp ({ node = ETApp (e, ts); _ }, es) ->
      let es =
        match es with
        | [ { typ = TUnit; node } ] -> assert (node = EUnit); []
        | _ -> es
      in
      Call (translate_expr env e, List.map (translate_type env) ts, List.map (translate_expr env) es)
  | EApp (e, es) ->
      let es =
        match es with
        | [ { typ = TUnit; node } ] -> assert (node = EUnit); []
        | _ -> es
      in
      Call (translate_expr env e, [], List.map (translate_expr env) es)
  | ETApp (_, _) ->
      failwith "TODO: ETApp"
  | EPolyComp _ ->
      failwith "unexpected: EPolyComp"

  | ELet (b, ({ node = EBufSub ({ node = EBound v_base; _ } as e_base, e_ofs); _ } as e1), e2) ->
      if Options.debug "rs-splits" then begin
        KPrint.bprintf "Translating: let %a = %a\n" PrintAst.Ops.pbind b PrintAst.Ops.pexpr e1;
        debug env
      end;

      let l = List.length env.vars in

      let index = Splits.index_of_expr l (translate_expr env e_ofs) (translate_type env e_ofs.typ) in
      (* We're splitting a variable x_base. *)
      let _, info_base = lookup env v_base in
      (* At the end of `path` is the variable we want to split. *)
      let info_base, path, index = Splits.split l info_base index in

      let e_nearest =
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
          MiniRust.(Field (find 0 env.vars, Splits.string_of_path_elem path_elem))
      in

      let split_at = match b.typ with TBuf (_, true) -> "split_at" | _ -> "split_at_mut" in
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

      Let (fst binding, e1, translate_expr_with_type env e2 t_ret)

  | ELet (b, ({ node = EBufCreate _ | EBufCreateL _; _ } as init), e2) ->
      let e1, t = translate_array env false init in
      let binding: MiniRust.binding = { name = b.node.name; typ = t; mut = true } in
      let env = push env binding in
      Let (binding, e1, translate_expr_with_type env e2 t_ret)
  | ELet (b, e1, e2) ->
      let e1 = translate_expr env e1 in
      let t = translate_type env b.typ in
      let binding : MiniRust.binding = { name = b.node.name; typ = t; mut = b.node.mut } in
      let env = push env binding in
      Let (binding, e1, translate_expr_with_type env e2 t_ret)
  | EFun _ ->
      failwith "unexpected: EFun"
  | EIfThenElse (e1, e2, e3) ->
      let e1 = translate_expr env e1 in
      let e2 = translate_expr_with_type env e2 t_ret in
      let e3 = if e3.node = EUnit then None else Some (translate_expr_with_type env e3 t_ret) in
      IfThenElse (e1, e2, e3)
  | ESequence _ ->
      failwith "unexpected: ESequence"
  | EAssign (e1, e2) ->
      Assign (translate_expr env e1, translate_expr env e2)
  | EBufCreate _ ->
      failwith "unexpected: EBufCreate"
  | EBufCreateL _ ->
      failwith "unexpected: EBufCreateL"
  | EBufRead (e1, e2) ->
      let e1 = translate_expr env e1 in
      let e2 = translate_expr_with_type env e2 (Constant SizeT) in
      Index (e1, e2)
  | EBufWrite (e1, e2, e3) ->
      let e1 = translate_expr env e1 in
      let e2 = translate_expr_with_type env e2 (Constant SizeT) in
      let e3 = translate_expr env e3 in
      Assign (Index (e1, e2), e3)
  | EBufSub (e1, e2) ->
      (* This is a fallback for the analysis above. Happens if, for instance, the pointer arithmetic
         appears in subexpression position (like, function call), in which case there's a chance
         this might still work! *)
      let e1 = translate_expr env e1 in
      let e2 = translate_expr_with_type env e2 (Constant SizeT) in
      Borrow (Mut, Index (e1, Range (Some e2, None, false)))
  | EBufDiff _ ->
      failwith "unexpected: EBufDiff"
  (* Silly pattern in Low*: for historical reasons, the blit operations takes a
     monotonic buffer (with any preorder) as its `src` argument. Since const pointers are an
     abstract type, there is an explicit coercion *to mutable* to pass a const pointer as the source
     of a bufblit operation. This is backwards, and should be fixed with an alternative `blit`
     function in the ConstBuffer module (or in the BufferOps module). *)
  | EBufBlit ({ node = ECast ({ typ = TBuf (_, true); _ } as src, TBuf (_, false)); _ }, src_index, dst, dst_index, len)
  | EBufBlit (src, src_index, dst, dst_index, len) ->
      let src = translate_expr env src in
      let src_index = translate_expr_with_type env src_index (Constant SizeT) in
      let dst = translate_expr env dst in
      let dst_index = translate_expr_with_type env dst_index (Constant SizeT) in
      let len = translate_expr_with_type env len (Constant SizeT) in
      MethodCall (
        Index (dst, H.range_with_len dst_index len),
        [ "copy_from_slice" ],
        [ Borrow (Shared, Index (src, H.range_with_len src_index len)) ])
  | EBufFill (dst, elt, len) ->
      let dst = translate_expr env dst in
      let elt = translate_expr env elt in
      let len = translate_expr_with_type env len (Constant SizeT) in
      if H.is_const len then
        MethodCall (
          Index (dst, H.range_with_len (Constant (SizeT, "0")) len),
          [ "copy_from_slice" ],
          [ Borrow (Shared, Array (Repeat (elt, len))) ])
      else
        MethodCall (
          Index (dst, H.range_with_len (Constant (SizeT, "0")) len),
          [ "copy_from_slice" ],
          [ Borrow (Shared, VecNew (Repeat (elt, len))) ])
  | EBufFree _ ->
      failwith "unexpected: EBufFree"
  | EBufNull ->
      VecNew (List [])
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

  | ESwitch _ ->
      failwith "TODO: ESwitch"
  | EEnum _ ->
      failwith "TODO: EEnum"
  | EFlat _ ->
      failwith "TODO: EFlat"
  | EField _ ->
      failwith "TODO: EField"
  | EBreak ->
      failwith "TODO: EBreak"
  | EContinue ->
      failwith "TODO: EContinue"
  | EReturn _ ->
      failwith "TODO: EReturn"
  | EWhile _ ->
      failwith "TODO: EWhile"
  | EFor (b, e_start, e_test, e_incr, e_body) ->
      (* b is in scope for e_test, e_incr, e_body! *)
      let e_end = match e_test.node, e_incr.node with
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
      let binding: MiniRust.binding = { name = b.node.name; typ = translate_type env b.typ; mut = false } in
      let e_start = translate_expr env e_start in
      let e_end = translate_expr env e_end in
      let e_body = translate_expr (push env binding) e_body in
      For (binding, Range (Some e_start, Some e_end, false), e_body)
  | ECast (e, t) ->
      As (translate_expr env e, translate_type env t)
  | EComment _ ->
      failwith "TODO: EComment"
  | EStandaloneComment _ ->
      failwith "TODO: EStandaloneComment"
  | EAddrOf e ->
      Borrow (Mut, translate_expr env e)

let make_poly (t: MiniRust.typ) n: MiniRust.typ =
  match t with
  | Function (0, ts, t) ->
      Function (n, ts, t)
  | _ ->
      failwith "impossible: make_poly received a non-function type"

let translate_decl env (d: Ast.decl) =
  let is_handled_primitively = function
    | [ "LowStar"; "BufferOps" ], s ->
        KString.starts_with s "op_Bang_Star__" ||
        KString.starts_with s "op_Star_Equals__"
    | _ ->
        false
  in
  match d with
  | Ast.DFunction (_, _, _, _, lid, _, _) when is_handled_primitively lid ->
      env, None

  | Ast.DFunction (_cc, flags, type_parameters, t, lid, args, body) ->
      assert (type_parameters = 0);
      if Options.debug "rs" then
        KPrint.bprintf "Ast.DFunction (%a)\n" PrintAst.Ops.plid lid;
      let args, body =
        if List.length args = 1 && (List.hd args).Ast.typ = TUnit then
          [], DeBruijn.subst Helpers.eunit 0 body
        else
          args, body
      in
      let parameters = List.map (fun (b: Ast.binder) ->
        let typ = translate_type env b.typ in
        let mut = false in
        { MiniRust.mut; name = b.Ast.node.Ast.name; typ }
      ) args in
      let return_type = translate_type env t in
      let name = translate_lid env lid in
      let env = push_global env lid (name, Function (type_parameters, List.map (fun x -> x.MiniRust.typ) parameters, return_type)) in
      let env0 = List.fold_left push env parameters in
      let body = translate_expr env0 body in
      let public = not (List.mem Common.Private flags) in
      let inline = List.mem Common.Inline flags in
      env, Some (MiniRust.Function { type_parameters; parameters; return_type; body; name; public; inline })

  | Ast.DGlobal (flags, lid, _, t, e) ->
      let body, typ = match e.node with
        | EBufCreate _ | EBufCreateL _ ->
            translate_array env true e
        | _ ->
            translate_expr env e, translate_type env t
      in
      if Options.debug "rs" then
        KPrint.bprintf "Ast.DGlobal (%a: %s)\n" PrintAst.Ops.plid lid (MiniRust.show_typ typ);
      let name = translate_lid env lid in
      let public = not (List.mem Common.Private flags) in
      let env = push_global env lid (name, typ) in
      env, Some (MiniRust.Constant { name; typ; body; public })

  | Ast.DExternal (_, _, type_parameters, lid, t, _param_names) ->
      let name = translate_unknown_lid lid in
      let env = push_global env lid (name, make_poly (translate_type env t) type_parameters) in
      env, None

  | Ast.DType (name, _, _, _) ->
      Warn.failwith "TODO: Ast.DType (%a)\n" PrintAst.Ops.plid name

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

let translate_files files =
  let failures = ref 0 in
  let env, files = List.fold_left (fun (env, files) (f, decls) ->
    let prefix = List.map String.lowercase_ascii (identify_path_components_rev f) in
    let prefix = compress_prefix (List.rev prefix) in
    if Options.debug "rs" then
      KPrint.bprintf "Translating file %s\n" (String.concat "::" prefix);
    let total = List.length decls in
    let env = { env with prefix } in
    let env, decls = List.fold_left (fun (env, decls) d ->
      try
        let env, d = translate_decl env d in
        env, d :: decls
      with e ->
        incr failures;
        KPrint.bprintf "%sERROR translating %a: %s%s\n%s\n" Ansi.red
          PrintAst.Ops.plid (Ast.lid_of_decl d)
          (Printexc.to_string e) Ansi.reset
          (Printexc.get_backtrace ());
        env, decls
    ) (env, []) decls in
    let decls = List.rev decls in
    if Options.debug "rs" then
      KPrint.bprintf "... translated file %s (%d/%d)\n" (String.concat "::" prefix) (List.length decls) total;
    let decls = KList.filter_some decls in
    env, (prefix, decls) :: files
  ) (empty, []) files in

  if Options.debug "rs" then
    LidMap.iter (fun lid (name, _) ->
      KPrint.bprintf "%a --> %s\n" PrintAst.Ops.plid lid (PrintMiniRust.string_of_name name)
    ) env.decls;

  if !failures > 0 then
    KPrint.bprintf "%s%d total errors%s\n" Ansi.red !failures Ansi.reset;

  List.rev files

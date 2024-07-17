(* AstToMiniRust generates code that only uses shared borrows; that is obviously
   incorrect, and so the purpose of this phase is to infer the minimum number of
   variables that need to be marked as `mut`, and the minimum number of borrows
   that need themselves to be `&mut`.

   This improves on an earlier iteration of the compilation scheme where
   everything was marked as mutable by default, a conservative, but suboptimal
   choice.

   We proceed as follows. We carry two sets of variables:
   - V stands for mutable variables, i.e. the set of variables that need to
     marked as mut using `let mut x = ...`. A variable needs to be marked as mut
     if it is mutably-borrowed, i.e. if `&mut x` occurs.
   - R stands for mutable references, i.e. the set of variables that have type
     `&mut T`. R is initially populated with function parameters.
   This is the state of our transformation, and as such, we return an augmented
   state after performing our inference, so that the callee can mark variables
   accordingly.

   An environment keeps track of the functions that have been visited already,
   along with their updated types.

   Finally, the transformation receives a contextual flag as an input parameter;
   the flag indicates whether the subexpression being visited (e.g. &x) needs to
   return a mutable borrow, meaning it gets rewritten (e.g. into &mut x) and the
   set V increases (because the Rust rule is that you can only write `&mut x` if
   `x` itself is declared with `let mut`).
*)

open MiniRust

module NameMap = Map.Make(Name)
module VarSet = Set.Make(Atom)

type env = {
  seen: typ list NameMap.t
}

type known = {
  v: VarSet.t;
  r: VarSet.t;
}

let add_mut_var a known =
  KPrint.bprintf "%s is let mut\n" (Ast.show_atom_t a);
  { known with v = VarSet.add a known.v }

let add_mut_borrow a known =
  KPrint.bprintf "%s is &mut\n" (Ast.show_atom_t a);
  { known with r = VarSet.add a known.r }

let want_mut_var a known =
  VarSet.mem a known.v

let want_mut_borrow a known =
  VarSet.mem a known.r

let is_mut_borrow = function
  | Ref (_, Mut, _) -> true
  (* Special-case for tuples; they should only occur with array slices *)
  | Tuple [Ref (_, Mut, _); Ref (_, Mut, _)] -> true
  | _ -> false

let make_mut_borrow = function
  | Ref (l, _, t) -> Ref (l, Mut, t)
  | Tuple [Ref (l1, _, t1); Ref (l2, _, t2)] -> Tuple [Ref (l1, Mut, t1); Ref (l2, Mut, t2)]
  | _ -> failwith "impossible: make_mut_borrow"

let assert_borrow = function
  | Ref (_, _, t) -> t
  | _ -> failwith "impossible: assert_borrow"

let retrieve_pair_type = function
  | Tuple [e1; e2] -> assert (e1 = e2); e1
  | _ -> failwith "impossible: retrieve_pair_type"

let rec infer (env: env) (expected: typ) (known: known) (e: expr): known * expr =
  match e with
  | Borrow (k, e) ->
      (* If we expect this borrow to be a mutable borrow, then we make it a mutable borrow
         (obviously!), and also remember that the variable x itself needs to be `let mut` *)
      if is_mut_borrow expected then
        match e with
        | Var _ ->
            failwith "impossible: missing open"
        | Open { atom; _ } ->
            add_mut_var atom known, Borrow (Mut, e)
        | _ ->
            failwith "TODO: borrowing something other than a variable"
      else
        let known, e = infer env (assert_borrow expected) known e in
        known, Borrow (k, e)

  | Open { atom; _ } ->
      (* If we expect this variable to be a mutable borrow, then we remember it and let the caller
         act accordingly. *)
      if is_mut_borrow expected then
        add_mut_borrow atom known, e
      else
        known, e

  | Let (b, e1, e2) ->
      KPrint.bprintf "[infer-mut,let] %a\n" PrintMiniRust.pexpr e;
      let a, e2 = open_ b e2 in
      KPrint.bprintf "[infer-mut,let] opened %s[%s]\n" b.name (show_atom_t a);
      let known, e2 = infer env expected known e2 in
      let mut_var = want_mut_var a known in
      let mut_borrow = want_mut_borrow a known in
      KPrint.bprintf "[infer-mut,let-done-e2] %s[%s]: %a let mut ? %b &mut ? %b\n" b.name
        (show_atom_t a)
        PrintMiniRust.ptyp b.typ mut_var mut_borrow;
      let t1 = if mut_borrow then make_mut_borrow b.typ else b.typ in
      let known, e1 = infer env t1 known e1 in
      known, Let ({ b with mut = mut_var; typ = t1 }, e1, close a (Var 0) (lift 1 e2))

  | Call (Name n, targs, es) ->
      if NameMap.mem n env.seen then
        (* TODO: substitute targs in ts -- for now, we assume we don't have a type-polymorphic
           function that gets instantiated with a reference type *)
        let ts = NameMap.find n env.seen in
        let known, es = List.fold_left2 (fun (known, es) e t ->
            let known, e = infer env t known e in
            known, e :: es
          ) (known, []) es ts
        in
        let es = List.rev es in
        known, Call (Name n, targs, es)
      else if n = ["lowstar";"ignore";"ignore"] then
        (* Since we do not have type-level substitutions in MiniRust, we special-case ignore here.
           Ideally, it would be added to builtins with `Bound 0` as a suitable type for the
           argument. *)
        let known, e = infer env (KList.one targs) known (KList.one es) in
        known, Call (Name n, targs, [ e ])
      else if n = [ "lib"; "memzero0"; "memzero" ] then (
        (* Same as ignore above *)
        assert (List.length es = 2);
        let e1, e2 = KList.two es in
        let known, e1 = infer env (Ref (None, Mut, Slice (KList.one targs))) known e1 in
        let known, e2 = infer env (Constant UInt32) known e2 in
        known, Call (Name n, targs, [ e1; e2 ])
      ) else (
        KPrint.bprintf "[infer-mut,call] recursing on %s\n" (String.concat " :: " n);
        failwith "TODO: recursion"
      )

  | Call (Operator o, [], _) -> begin match o with
      (* Most operators are wrapping and were translated to a methodcall.
         We list the few remaining ones here *)
      | BOr | BAnd | BXor | BNot
      | Eq | Neq | Lt | Lte | Gt | Gte
      | And | Or | Xor | Not -> known, e
      | _ ->
        failwith "TODO: operator not supported"
    end

  | Call _ ->
      failwith "TODO: Call"

  | Assign (Open { atom; _ }, e3, t) ->
      KPrint.bprintf "[infer-mut,assign] %a\n" PrintMiniRust.pexpr e;
      let known, e3 = infer env t known e3 in
      add_mut_var atom known, e3

  | Assign (Index (Open { atom; _ } as e1, e2), e3, t) 
  (* Special-case when we perform a field assignment that comes from
     a slice. This is the only case where we use native Rust tuples.
     In this case, we mark the atom as mutable, and will replace
     the corresponding call to split by split_at_mut when we reach
      let-binding.
   *)
  | Assign (Index (Field (Open {atom;_}, "0") as e1, e2), e3, t)
  | Assign (Index (Field (Open {atom;_}, "1") as e1, e2), e3, t)
  ->
      KPrint.bprintf "[infer-mut,assign] %a\n" PrintMiniRust.pexpr e;
      let known = add_mut_borrow atom known in
      let known, e2 = infer env usize known e2 in
      let known, e3 = infer env t known e3 in
      known, Assign (Index (e1, e2), e3, t)

  | Assign (Index (Borrow (_, (Open { atom; _ } as e1)), e2), e3, t) ->
      KPrint.bprintf "[infer-mut,assign] %a\n" PrintMiniRust.pexpr e;
      let known = add_mut_var atom known in
      let known, e2 = infer env usize known e2 in
      let known, e3 = infer env t known e3 in
      known, Assign (Index (Borrow (Mut, e1), e2), e3, t)

  | Assign _ ->
      failwith "TODO: unknown assignment"

  | Var _
  | Array _
  | VecNew _
  | Name _
  | Constant _
  | ConstantString _
  | Unit
  | Panic _
  | Operator _ ->
      known, e

  | IfThenElse (e1, e2, e3) ->
      let known, e1 = infer env bool known e1 in
      let known, e2 = infer env expected known e2 in
      let known, e3 =
        match e3 with
        | Some e3 ->
            let known, e3 = infer env expected known e3 in
            known, Some e3
        | None ->
            known, None
      in
      known, IfThenElse (e1, e2, e3)

  | As (e, t) ->
      (* Not really correct, but As is only used for integer casts *)
      let known, e = infer env t known e in
      known, As (e, t)

  | For (b, e1, e2) ->
      let known, e2 = infer env Unit known e2 in
      known, For (b, e1, e2)

  | While (e1, e2) ->
      let known, e2 = infer env Unit known e2 in
      known, While (e1, e2)

  | MethodCall (e1, m, e2) ->
      (* There are only a few instances of these generated by AstToMiniRust, so we just review them
         all here. Note that there are two possible strategies: AstToMiniRust could use an IndexMut
         AST node to indicate e.g. that the destination of `copy_from_slice` ought to be mutable, or
         we just bake that knowledge in right here. *)
      begin match m with
      | [ "wrapping_add" ] | [ "wrapping_div" ] | [ "wrapping_mul" ] 
      | [ "wrapping_neg" ] | [ "wrapping_rem" ] | [ "wrapping_shl" ]
      | [ "wrapping_shr" ] | [ "wrapping_sub" ] ->
          known, MethodCall (e1, m, e2)
      | ["split_at"] ->
          assert (List.length e2 = 1);
          let known, e2 = infer env usize known (List.hd e2) in
          let t1 = retrieve_pair_type expected in
          let known, e1 = infer env t1 known e1 in
          if is_mut_borrow expected then
            known, MethodCall (e1, ["split_at_mut"], [e2])
          else
            known, MethodCall (e1, m, [e2])
      | ["copy_from_slice"] -> begin match e1 with
          | Index (dst, range) ->
            assert (List.length e2 = 1);
            (* We do not have access to the types of e1 and e2. However, the concrete
               type should not matter during mut inference, we thus use Unit as a default *)
            let known, dst = infer env (Ref (None, Mut, Unit)) known dst in
            let known, e2 = infer env (Ref (None, Shared, Unit)) known (List.hd e2) in
            known, MethodCall (Index (dst, range), m, [e2])
          (* The AstToMiniRust translation should always introduce an index
              as the left argument of copy_from_slice *)
          | _ -> failwith "ill-formed copy_from_slice"
          end
      | _ ->
          KPrint.bprintf "%a\n" PrintMiniRust.pexpr e;
          failwith "TODO: MethodCall"
      end

  | Range (e1, e2, b) ->
      known, Range (e1, e2, b)

  | Struct _ ->
      (* TODO: This should very likely be modified depending on the current struct
         in known. *)
      known, e

  | Match _ ->
      failwith "TODO: Match"

  | Index (e1, e2) ->
      (* The cases where we perform an assignment on an index should be caught
         earlier. This should therefore only occur when accessing a variable
         in an array *)
      let expected = Ref (None, Shared, expected) in
      let known, e1 = infer env expected known e1 in
      let known, e2 = infer env usize known e2 in
      known, Index (e1, e2)

  (* Special case for array slices. This occurs, e.g., when calling a function with 
     a struct field *)
  | Field (Open { atom; _ }, "0") | Field (Open { atom; _}, "1") ->
      if is_mut_borrow expected then
        add_mut_borrow atom known, e
      else known, e

  | Field _ ->
      (* We should be able to ignore this case, on the basis that we are not going to get any
         mutability constraints from a field expression. However, we need to modify all of the cases
         above (such as assignment) to handle the case where the assignee is a field. *)
      known, e

  | Deref _ ->
      failwith "TODO: Deref"

(* We store here a list of builtins, with the types of their arguments.
   Type substitutions are currently not supported, functions with generic
   args should be added directly to Call in infer *)
let builtins : (name * typ list) list = [
  (* FStar.UInt128 *)
  [ "fstar"; "uint128"; "uint64_to_uint128" ], [Constant UInt64];
  [ "fstar"; "uint128"; "uint128_to_uint64" ], [Name (["fstar"; "uint128"; "uint128"], [])];
  [ "fstar"; "uint128"; "add_mod" ],
      [Name (["fstar"; "uint128"; "uint128"], []); Name (["fstar"; "uint128"; "uint128"], [])];
  [ "fstar"; "uint128"; "shift_right" ],
      [Name (["fstar"; "uint128"; "uint128"], []); Constant UInt32];

  (* LowStar.Endianness *)
  [ "lowstar"; "endianness"; "load64_le" ], [Ref (None, Shared, Constant UInt8)];
  [ "lowstar"; "endianness"; "store64_le" ], [Ref (None, Mut, Constant UInt8)];
]

let infer_mut_borrows files =
  (* Map.of_list is only available from OCaml 5.1 onwards *)
  let env = { seen = List.to_seq builtins |> NameMap.of_seq } in
  let known = { v = VarSet.empty; r = VarSet.empty } in
  let _, files =
    List.fold_left (fun (env, files) (filename, decls) ->
      let env, decls = List.fold_left (fun (env, decls) decl ->
        match decl with
        | Function ({ name; body; return_type; parameters; _ } as f) ->
            KPrint.bprintf "[infer-mut] visiting %s\n%a\n" (String.concat "." name)
              PrintMiniRust.pdecl decl;
            let atoms, body =
              List.fold_right (fun binder (atoms, e) ->
                let a, e = open_ binder e in
                KPrint.bprintf "[infer-mut] opened %s[%s]\n%a\n" binder.name (show_atom_t a) PrintMiniRust.pexpr e;
                a :: atoms, e
              ) parameters ([], body)
            in
            KPrint.bprintf "[infer-mut] done opening %s\n%a\n" (String.concat "." name)
              PrintMiniRust.pexpr body;
            let known, body = infer env return_type known body in
            let parameters, body =
              List.fold_left2 (fun (parameters, e) (binder: binding) atom ->
                let e = close atom (Var 0) (lift 1 e) in
                KPrint.bprintf "[infer-mut] closed %s[%s]\n%a\n" binder.name (show_atom_t atom) PrintMiniRust.pexpr e;
                let mut = want_mut_var atom known in
                let typ = if want_mut_borrow atom known then make_mut_borrow binder.typ else binder.typ in
                { binder with mut; typ } :: parameters, e
              ) ([], body) parameters atoms
            in
            let parameters = List.rev parameters in
            let env = { seen = NameMap.add name (List.map (fun (x: binding) -> x.typ) parameters) env.seen } in
            env, Function { f with body; parameters } :: decls
        | _ ->
            env, decl :: decls
      ) (env, []) decls in
      let decls = List.rev decls in
      env, (filename, decls) :: files
    ) (env, []) files
  in
  List.rev files

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
  seen: typ list NameMap.t;
  structs: MiniRust.struct_field list NameMap.t;
}

type known = {
  structs: MiniRust.struct_field list NameMap.t;
  v: VarSet.t;
  r: VarSet.t;
}

let assert_borrow = function
  | Ref (_, _, t) -> t
  | _ -> failwith "impossible: assert_borrow"

let assert_name (t: typ option) = match t with
  | Some (Name (n, _)) -> n
  | _ -> failwith "impossible: assert_name"

let add_mut_var a known =
  (* KPrint.bprintf "%s is let mut\n" (Ast.show_atom_t a); *)
  { known with v = VarSet.add a known.v }

let add_mut_borrow a known =
  (* KPrint.bprintf "%s is &mut\n" (Ast.show_atom_t a); *)
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
  | Vec t -> Vec t
  | _ -> failwith "impossible: make_mut_borrow"

let add_mut_field ty f known =
  let n = assert_name ty in
  let fields = NameMap.find n known.structs in
  (* Update the mutability of the field element *)
  let fields = List.map (fun (sf: MiniRust.struct_field) ->
    if sf.name = f then {sf with typ = make_mut_borrow sf.typ} else sf) fields in
  {known with structs = NameMap.add n fields known.structs}

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
        | Index (e1, (Range _ as r))  ->
            let known, e1 = infer env expected known e1 in
            known, Borrow (Mut, Index (e1, r))

        | Field (Open _, "0", None)
        | Field (Open _, "1", None) -> failwith "TODO: borrowing slices"

        | Field (Open {atom; _}, _, _) ->
            add_mut_var atom known, Borrow (Mut, e)

        | Field (Deref (Open {atom; _}), _, _) ->
            add_mut_borrow atom known, Borrow (Mut, e)

        | Field (Index (Open {atom; _}, _), _, _) ->
            add_mut_borrow atom known, Borrow (Mut, e)

        | _ ->
            KPrint.bprintf "[infer-mut, borrow] borrwing %a is not supported\n" PrintMiniRust.pexpr e;
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
      (* KPrint.bprintf "[infer-mut,let] %a\n" PrintMiniRust.pexpr e; *)
      let a, e2 = open_ b e2 in
      (* KPrint.bprintf "[infer-mut,let] opened %s[%s]\n" b.name (show_atom_t a); *)
      let known, e2 = infer env expected known e2 in
      let mut_var = want_mut_var a known in
      let mut_borrow = want_mut_borrow a known in
      (* KPrint.bprintf "[infer-mut,let-done-e2] %s[%s]: %a let mut ? %b &mut ? %b\n" b.name
        (show_atom_t a)
        PrintMiniRust.ptyp b.typ mut_var mut_borrow; *)
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
        let known, e2 = infer env u32 known e2 in
        known, Call (Name n, targs, [ e1; e2 ])
      ) else (
        KPrint.bprintf "[infer-mut,call] recursing on %s\n" (String.concat " :: " n);
        failwith "TODO: recursion"
      )

  | Call (Operator o, [], _) -> begin match o with
      (* Most operators are wrapping and were translated to a methodcall.
         We list the few remaining ones here *)
      | Add | Sub
      | BOr | BAnd | BXor | BNot
      | Eq | Neq | Lt | Lte | Gt | Gte
      | And | Or | Xor | Not -> known, e
      | _ ->
        KPrint.bprintf "[infer-mut,call] %a not supported\n" PrintMiniRust.pexpr e;
        failwith "TODO: operator not supported"
    end

  | Call _ ->
      failwith "TODO: Call"

  (* atom = e3 *)
  | Assign (Open { atom; _ }, e3, t) ->
      (* KPrint.bprintf "[infer-mut,assign] %a\n" PrintMiniRust.pexpr e; *)
      let known, e3 = infer env t known e3 in
      add_mut_var atom known, e3

  (* atom[e2] = e2 *)
  | Assign (Index (Open { atom; _ } as e1, e2), e3, t) 

  (* Special-case when we perform a field assignment that comes from
     a slice. This is the only case where we use native Rust tuples.
     In this case, we mark the atom as mutable, and will replace
     the corresponding call to split by split_at_mut when we reach
      let-binding.
   *)
  (* atom.0[e2] = e3 *)
  | Assign (Index (Field (Open {atom;_}, "0", None) as e1, e2), e3, t)
  (* atom.1[e2] = e3 *)
  | Assign (Index (Field (Open {atom;_}, "1", None) as e1, e2), e3, t) ->
      (* KPrint.bprintf "[infer-mut,assign] %a\n" PrintMiniRust.pexpr e; *)
      let known = add_mut_borrow atom known in
      let known, e2 = infer env usize known e2 in
      let known, e3 = infer env t known e3 in
      known, Assign (Index (e1, e2), e3, t)

  (* x.f[e2] = e3 *)
  | Assign (Index (Field (_, f, st) as e1, e2), e3, t) ->
      let known = add_mut_field st f known in
      let known, e2 = infer env usize known e2 in
      let known, e3 = infer env t known e3 in
      known, Assign (Index (e1, e2), e3, t)

  (* (&atom)[e2] = e3 *)
  | Assign (Index (Borrow (_, (Open { atom; _ } as e1)), e2), e3, t) ->
      (* KPrint.bprintf "[infer-mut,assign] %a\n" PrintMiniRust.pexpr e; *)
      let known = add_mut_var atom known in
      let known, e2 = infer env usize known e2 in
      let known, e3 = infer env t known e3 in
      known, Assign (Index (Borrow (Mut, e1), e2), e3, t)

  | Assign (Field (_, "0", None), _, _)
  | Assign (Field (_, "1", None), _, _) ->
      failwith "TODO: assignment on slice"

  (* (atom.f)[e2] = e3 *)
  | Assign (Field (Index ((Open {atom; _} as e1), e2), f, st), e3, t) ->
      let known = add_mut_borrow atom known in
      let known, e2 = infer env usize known e2 in
      let known, e3 = infer env t known e3 in
      known, Assign (Field (Index (e1, e2), f, st), e3, t)

  (* (&n)[e2] = e3 *)
  | Assign (Index (Borrow (_, Name n), e2), e3, t) ->
      (* This case should only occur for globals. For now, we simply mutably borrow it *)
      let known, e2 = infer env usize known e2 in
      let known, e3 = infer env t known e3 in
      known, Assign (Index (Borrow (Mut, Name n), e2), e3, t)

  (* (&(&atom)[e2])[e3] = e4 *)
  | Assign (Index (Borrow (_, Index (Borrow (_, (Open {atom; _} as e1)), e2)), e3), e4, t) ->
      let known = add_mut_var atom known in
      let known, e2 = infer env usize known e2 in
      let known, e3 = infer env usize known e3 in
      let known, e4 = infer env t known e4 in
      known, Assign (Index (Borrow (Mut, Index (Borrow (Mut, e1), e2)), e3), e4, t)

  | Assign _ ->
      KPrint.bprintf "[infer-mut,assign] %a unsupported\n" PrintMiniRust.pexpr e;
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
      | [ "wrapping_shr" ] | [ "wrapping_sub" ]
      | [ "to_vec" ] ->
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
      | [ "push" ] -> begin match e1 with
          | Open {atom; _} -> add_mut_var atom known, MethodCall (e1, m, e2)
          | _ -> failwith "TODO: push on complex expressions"
          end
      | _ ->
          KPrint.bprintf "%a unsupported\n" PrintMiniRust.pexpr e;
          failwith "TODO: MethodCall"
      end

  | Range (e1, e2, b) ->
      known, Range (e1, e2, b)

  | Struct (name, _es) ->
      (* The declaration of the struct should have been traversed beforehand, hence
         it should be in the map *)
      let _fields_mut = NameMap.find name known.structs in
      (* TODO: This should be modified depending on the current struct
         in known. *)
      known, e

  | Match (e, arms) ->
      (* For now, all pattern-matching occur on simple terms, e.g., an enum for an
         alg, hence we do not mutify the scrutinee. If this happens to be needed,
         we would need to add the expected type of the scrutinee to the Match node,
         similar to what is done for Assign and Field, in order to recurse on
         the scrutinee *)
      let known, arms = List.fold_left_map (fun known (pat, e) ->
          let known, e = infer env expected known e in
          known, (pat, e)
        ) known arms in
      known, Match (e, arms) 

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
  | Field (Open { atom; _ }, "0", None) | Field (Open { atom; _}, "1", None) ->
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
  (* EverCrypt.TargetConfig. The following two functions are handwritten,
     while the rest of EverCrypt is generated *)
  [ "evercrypt"; "targetconfig"; "has_vec128_not_avx" ], [];
  [ "evercrypt"; "targetconfig"; "has_vec256_not_avx2" ], [];

  (* FStar.UInt8 *)
  [ "fstar"; "uint8"; "eq_mask" ], [ u8; u8 ];
  [ "fstar"; "uint8"; "gte_mask" ], [ u8; u8 ];

  (* FStar.UInt16 *)
  [ "fstar"; "uint16"; "eq_mask" ], [ u16; u16 ];
  [ "fstar"; "uint16"; "gte_mask" ], [ u16; u16 ];

  (* FStar.UInt32 *)
  [ "fstar"; "uint32"; "eq_mask" ], [ u32; u32 ];
  [ "fstar"; "uint32"; "gte_mask" ], [ u32; u32 ];

  (* FStar.UInt64 *)
  [ "fstar"; "uint64"; "eq_mask" ], [ u64; u64 ];
  [ "fstar"; "uint64"; "gte_mask" ], [ u64; u64 ];


  (* FStar.UInt128 *)
  [ "fstar"; "uint128"; "add" ],
      [Name (["fstar"; "uint128"; "uint128"], []); Name (["fstar"; "uint128"; "uint128"], [])];
  [ "fstar"; "uint128"; "add_mod" ],
      [Name (["fstar"; "uint128"; "uint128"], []); Name (["fstar"; "uint128"; "uint128"], [])];
  [ "fstar"; "uint128"; "sub" ],
      [Name (["fstar"; "uint128"; "uint128"], []); Name (["fstar"; "uint128"; "uint128"], [])];
  [ "fstar"; "uint128"; "sub_mod" ],
      [Name (["fstar"; "uint128"; "uint128"], []); Name (["fstar"; "uint128"; "uint128"], [])];
  [ "fstar"; "uint128"; "logand" ],
      [Name (["fstar"; "uint128"; "uint128"], []); Name (["fstar"; "uint128"; "uint128"], [])];
  [ "fstar"; "uint128"; "logxor" ],
      [Name (["fstar"; "uint128"; "uint128"], []); Name (["fstar"; "uint128"; "uint128"], [])];
  [ "fstar"; "uint128"; "logor" ],
      [Name (["fstar"; "uint128"; "uint128"], []); Name (["fstar"; "uint128"; "uint128"], [])];
  [ "fstar"; "uint128"; "lognot" ],
      [Name (["fstar"; "uint128"; "uint128"], [])];
  [ "fstar"; "uint128"; "shift_left" ],
      [Name (["fstar"; "uint128"; "uint128"], []); u32];
  [ "fstar"; "uint128"; "shift_right" ],
      [Name (["fstar"; "uint128"; "uint128"], []); u32];
  [ "fstar"; "uint128"; "eq" ],
      [Name (["fstar"; "uint128"; "uint128"], []); Name (["fstar"; "uint128"; "uint128"], [])];
  [ "fstar"; "uint128"; "gt" ],
      [Name (["fstar"; "uint128"; "uint128"], []); Name (["fstar"; "uint128"; "uint128"], [])];
  [ "fstar"; "uint128"; "lt" ],
      [Name (["fstar"; "uint128"; "uint128"], []); Name (["fstar"; "uint128"; "uint128"], [])];
  [ "fstar"; "uint128"; "gte" ],
      [Name (["fstar"; "uint128"; "uint128"], []); Name (["fstar"; "uint128"; "uint128"], [])];
  [ "fstar"; "uint128"; "lte" ],
      [Name (["fstar"; "uint128"; "uint128"], []); Name (["fstar"; "uint128"; "uint128"], [])];
  [ "fstar"; "uint128"; "eq_mask" ],
      [Name (["fstar"; "uint128"; "uint128"], []); Name (["fstar"; "uint128"; "uint128"], [])];
  [ "fstar"; "uint128"; "gte_mask" ],
      [Name (["fstar"; "uint128"; "uint128"], []); Name (["fstar"; "uint128"; "uint128"], [])];
  [ "fstar"; "uint128"; "uint64_to_uint128" ], [u64];
  [ "fstar"; "uint128"; "uint128_to_uint64" ], [Name (["fstar"; "uint128"; "uint128"], [])];
  [ "fstar"; "uint128"; "mul32" ], [u64; u32];
  [ "fstar"; "uint128"; "mul_wide" ], [u64; u32];

  (* Lib.Inttypes_Intrinsics *)
  [ "lib"; "inttypes_intrinsics"; "add_carry_u32"], [ u32; u32; u32; Ref (None, Mut, Slice u32) ];
  [ "lib"; "inttypes_intrinsics"; "sub_borrow_u32"], [ u32; u32; u32; Ref (None, Mut, Slice u32) ];
  [ "lib"; "inttypes_intrinsics"; "add_carry_u64"], [ u64; u64; u64; Ref (None, Mut, Slice u64) ];
  [ "lib"; "inttypes_intrinsics"; "sub_borrow_u64"], [ u64; u64; u64; Ref (None, Mut, Slice u64) ];


  (* Lib.IntVector_intrinsics, Vec128 *)
  [ "lib"; "intvector_intrinsics"; "vec128_add32"],
    [Name (["lib"; "intvector_intrinsics"; "vec128"], []);
     Name (["lib"; "intvector_intrinsics"; "vec128"], [])];
  [ "lib"; "intvector_intrinsics"; "vec128_add64"],
    [Name (["lib"; "intvector_intrinsics"; "vec128"], []);
     Name (["lib"; "intvector_intrinsics"; "vec128"], [])];
  [ "lib"; "intvector_intrinsics"; "vec128_and"],
    [Name (["lib"; "intvector_intrinsics"; "vec128"], []);
     Name (["lib"; "intvector_intrinsics"; "vec128"], [])];
  [ "lib"; "intvector_intrinsics"; "vec128_eq64"],
    [Name (["lib"; "intvector_intrinsics"; "vec128"], []);
     Name (["lib"; "intvector_intrinsics"; "vec128"], [])];
  [ "lib"; "intvector_intrinsics"; "vec128_extract64"],
    [Name (["lib"; "intvector_intrinsics"; "vec128"], []); u32];
  [ "lib"; "intvector_intrinsics"; "vec128_gt64"],
    [Name (["lib"; "intvector_intrinsics"; "vec128"], []);
     Name (["lib"; "intvector_intrinsics"; "vec128"], [])];
  [ "lib"; "intvector_intrinsics"; "vec128_insert64"],
    [Name (["lib"; "intvector_intrinsics"; "vec128"], []); u64; u32];
  [ "lib"; "intvector_intrinsics"; "vec128_interleave_low32"],
    [Name (["lib"; "intvector_intrinsics"; "vec128"], []);
     Name (["lib"; "intvector_intrinsics"; "vec128"], [])];
  [ "lib"; "intvector_intrinsics"; "vec128_interleave_low64"],
    [Name (["lib"; "intvector_intrinsics"; "vec128"], []);
     Name (["lib"; "intvector_intrinsics"; "vec128"], [])];
  [ "lib"; "intvector_intrinsics"; "vec128_interleave_high32"],
    [Name (["lib"; "intvector_intrinsics"; "vec128"], []);
     Name (["lib"; "intvector_intrinsics"; "vec128"], [])];
  [ "lib"; "intvector_intrinsics"; "vec128_interleave_high64"],
    [Name (["lib"; "intvector_intrinsics"; "vec128"], []);
     Name (["lib"; "intvector_intrinsics"; "vec128"], [])];
  [ "lib"; "intvector_intrinsics"; "vec128_load32"], [u32];
  [ "lib"; "intvector_intrinsics"; "vec128_load32s"], [u32; u32; u32; u32];
  [ "lib"; "intvector_intrinsics"; "vec128_load32_be"], [Ref (None, Shared, Slice u8)];
  [ "lib"; "intvector_intrinsics"; "vec128_load32_le"], [Ref (None, Shared, Slice u8)];
  [ "lib"; "intvector_intrinsics"; "vec128_load64"], [u64];
  [ "lib"; "intvector_intrinsics"; "vec128_load64_le"], [Ref (None, Shared, Slice u8)];
  [ "lib"; "intvector_intrinsics"; "vec128_lognot"],
    [Name (["lib"; "intvector_intrinsics"; "vec128"], [])];
  [ "lib"; "intvector_intrinsics"; "vec128_mul32"],
    [Name (["lib"; "intvector_intrinsics"; "vec128"], []);
     Name (["lib"; "intvector_intrinsics"; "vec128"], [])];
  [ "lib"; "intvector_intrinsics"; "vec128_mul64"],
    [Name (["lib"; "intvector_intrinsics"; "vec128"], []);
     Name (["lib"; "intvector_intrinsics"; "vec128"], [])];
  [ "lib"; "intvector_intrinsics"; "vec128_or"],
    [Name (["lib"; "intvector_intrinsics"; "vec128"], []);
     Name (["lib"; "intvector_intrinsics"; "vec128"], [])];
  [ "lib"; "intvector_intrinsics"; "vec128_rotate_left32"],
    [Name (["lib"; "intvector_intrinsics"; "vec128"], []); u32];
  [ "lib"; "intvector_intrinsics"; "vec128_rotate_right32"],
    [Name (["lib"; "intvector_intrinsics"; "vec128"], []); u32];
  [ "lib"; "intvector_intrinsics"; "vec128_rotate_right_lanes32"],
    [Name (["lib"; "intvector_intrinsics"; "vec128"], []); u32];
  [ "lib"; "intvector_intrinsics"; "vec128_shift_left64"],
    [Name (["lib"; "intvector_intrinsics"; "vec128"], []); u32];
  [ "lib"; "intvector_intrinsics"; "vec128_shift_right32"],
    [Name (["lib"; "intvector_intrinsics"; "vec128"], []); u32];
  [ "lib"; "intvector_intrinsics"; "vec128_shift_right64"],
    [Name (["lib"; "intvector_intrinsics"; "vec128"], []); u32];
  [ "lib"; "intvector_intrinsics"; "vec128_smul64"],
    [Name (["lib"; "intvector_intrinsics"; "vec128"], []); u64];
  [ "lib"; "intvector_intrinsics"; "vec128_store32_be"],
    [Ref (None, Mut, Slice u8); Name (["lib"; "intvector_intrinsics"; "vec128"], [])];
  [ "lib"; "intvector_intrinsics"; "vec128_store32_le"],
    [Ref (None, Mut, Slice u8); Name (["lib"; "intvector_intrinsics"; "vec128"], [])];
  [ "lib"; "intvector_intrinsics"; "vec128_sub64"],
    [Name (["lib"; "intvector_intrinsics"; "vec128"], []);
     Name (["lib"; "intvector_intrinsics"; "vec128"], [])];
  [ "lib"; "intvector_intrinsics"; "vec128_xor"],
    [Name (["lib"; "intvector_intrinsics"; "vec128"], []);
     Name (["lib"; "intvector_intrinsics"; "vec128"], [])];

  (* Lib.IntVector_intrinsics, Vec256 *)
  [ "lib"; "intvector_intrinsics"; "vec256_add32"],
    [Name (["lib"; "intvector_intrinsics"; "vec256"], []);
     Name (["lib"; "intvector_intrinsics"; "vec256"], [])];
  [ "lib"; "intvector_intrinsics"; "vec256_add64"],
    [Name (["lib"; "intvector_intrinsics"; "vec256"], []);
     Name (["lib"; "intvector_intrinsics"; "vec256"], [])];
  [ "lib"; "intvector_intrinsics"; "vec256_and"],
    [Name (["lib"; "intvector_intrinsics"; "vec256"], []);
     Name (["lib"; "intvector_intrinsics"; "vec256"], [])];
  [ "lib"; "intvector_intrinsics"; "vec256_eq64"],
    [Name (["lib"; "intvector_intrinsics"; "vec256"], []);
     Name (["lib"; "intvector_intrinsics"; "vec256"], [])];
  [ "lib"; "intvector_intrinsics"; "vec256_extract64"],
    [Name (["lib"; "intvector_intrinsics"; "vec256"], []); u32];
  [ "lib"; "intvector_intrinsics"; "vec256_gt64"],
    [Name (["lib"; "intvector_intrinsics"; "vec256"], []);
     Name (["lib"; "intvector_intrinsics"; "vec256"], [])];
  [ "lib"; "intvector_intrinsics"; "vec256_insert64"],
    [Name (["lib"; "intvector_intrinsics"; "vec256"], []); u64; u32];
  [ "lib"; "intvector_intrinsics"; "vec256_interleave_low32"],
    [Name (["lib"; "intvector_intrinsics"; "vec256"], []);
     Name (["lib"; "intvector_intrinsics"; "vec256"], [])];
  [ "lib"; "intvector_intrinsics"; "vec256_interleave_low64"],
    [Name (["lib"; "intvector_intrinsics"; "vec256"], []);
     Name (["lib"; "intvector_intrinsics"; "vec256"], [])];
  [ "lib"; "intvector_intrinsics"; "vec256_interleave_low128"],
    [Name (["lib"; "intvector_intrinsics"; "vec256"], []);
     Name (["lib"; "intvector_intrinsics"; "vec256"], [])];
  [ "lib"; "intvector_intrinsics"; "vec256_interleave_high32"],
    [Name (["lib"; "intvector_intrinsics"; "vec256"], []);
     Name (["lib"; "intvector_intrinsics"; "vec256"], [])];
  [ "lib"; "intvector_intrinsics"; "vec256_interleave_high64"],
    [Name (["lib"; "intvector_intrinsics"; "vec256"], []);
     Name (["lib"; "intvector_intrinsics"; "vec256"], [])];
  [ "lib"; "intvector_intrinsics"; "vec256_interleave_high128"],
    [Name (["lib"; "intvector_intrinsics"; "vec256"], []);
     Name (["lib"; "intvector_intrinsics"; "vec256"], [])];
  [ "lib"; "intvector_intrinsics"; "vec256_load32"], [u32];
  [ "lib"; "intvector_intrinsics"; "vec256_load32s"], [u32; u32; u32; u32; u32; u32; u32; u32]; 
  [ "lib"; "intvector_intrinsics"; "vec256_load32_be"], [Ref (None, Shared, Slice u8)];
  [ "lib"; "intvector_intrinsics"; "vec256_load32_le"], [Ref (None, Shared, Slice u8)];
  [ "lib"; "intvector_intrinsics"; "vec256_load64"], [u64];
  [ "lib"; "intvector_intrinsics"; "vec256_load64s"], [u64; u64; u64; u64];
  [ "lib"; "intvector_intrinsics"; "vec256_load64_be"], [Ref (None, Shared, Slice u8)];
  [ "lib"; "intvector_intrinsics"; "vec256_load64_le"], [Ref (None, Shared, Slice u8)];
  [ "lib"; "intvector_intrinsics"; "vec256_lognot"],
    [Name (["lib"; "intvector_intrinsics"; "vec256"], [])];
  [ "lib"; "intvector_intrinsics"; "vec256_mul64"],
    [Name (["lib"; "intvector_intrinsics"; "vec256"], []);
     Name (["lib"; "intvector_intrinsics"; "vec256"], [])];
  [ "lib"; "intvector_intrinsics"; "vec256_or"],
    [Name (["lib"; "intvector_intrinsics"; "vec256"], []);
     Name (["lib"; "intvector_intrinsics"; "vec256"], [])];
  [ "lib"; "intvector_intrinsics"; "vec256_rotate_left32"],
    [Name (["lib"; "intvector_intrinsics"; "vec256"], []); u32];
  [ "lib"; "intvector_intrinsics"; "vec256_rotate_right32"],
    [Name (["lib"; "intvector_intrinsics"; "vec256"], []); u32];
  [ "lib"; "intvector_intrinsics"; "vec256_rotate_right64"],
    [Name (["lib"; "intvector_intrinsics"; "vec256"], []); u32];
  [ "lib"; "intvector_intrinsics"; "vec256_rotate_right_lanes64"],
    [Name (["lib"; "intvector_intrinsics"; "vec256"], []); u32];
  [ "lib"; "intvector_intrinsics"; "vec256_shift_left64"],
    [Name (["lib"; "intvector_intrinsics"; "vec256"], []); u32];
  [ "lib"; "intvector_intrinsics"; "vec256_shift_right"],
    [Name (["lib"; "intvector_intrinsics"; "vec256"], []); u32];
  [ "lib"; "intvector_intrinsics"; "vec256_shift_right32"],
    [Name (["lib"; "intvector_intrinsics"; "vec256"], []); u32];
  [ "lib"; "intvector_intrinsics"; "vec256_shift_right64"],
    [Name (["lib"; "intvector_intrinsics"; "vec256"], []); u32];
  [ "lib"; "intvector_intrinsics"; "vec256_smul64"],
    [Name (["lib"; "intvector_intrinsics"; "vec256"], []); u64];
  [ "lib"; "intvector_intrinsics"; "vec256_store32_be"],
    [Ref (None, Mut, Slice u8); Name (["lib"; "intvector_intrinsics"; "vec256"], [])];
  [ "lib"; "intvector_intrinsics"; "vec256_store32_le"],
    [Ref (None, Mut, Slice u8); Name (["lib"; "intvector_intrinsics"; "vec256"], [])];
  [ "lib"; "intvector_intrinsics"; "vec256_store64_be"],
    [Ref (None, Mut, Slice u8); Name (["lib"; "intvector_intrinsics"; "vec256"], [])];
  [ "lib"; "intvector_intrinsics"; "vec256_store64_le"],
    [Ref (None, Mut, Slice u8); Name (["lib"; "intvector_intrinsics"; "vec256"], [])];
  [ "lib"; "intvector_intrinsics"; "vec256_sub64"],
    [Name (["lib"; "intvector_intrinsics"; "vec256"], []);
     Name (["lib"; "intvector_intrinsics"; "vec256"], [])];
  [ "lib"; "intvector_intrinsics"; "vec256_xor"],
    [Name (["lib"; "intvector_intrinsics"; "vec256"], []);
     Name (["lib"; "intvector_intrinsics"; "vec256"], [])];

  (* Lib.RandomBuffer_System *)
  [ "lib"; "randombuffer_system"; "randombytes"], [Ref (None, Mut, Slice u8); u32]; 

  (* LowStar.Endianness, little-endian *)
  [ "lowstar"; "endianness"; "load16_le" ], [Ref (None, Shared, Slice u8)];
  [ "lowstar"; "endianness"; "store16_le" ], [Ref (None, Mut, Slice u8); u16];
  [ "lowstar"; "endianness"; "load32_le" ], [Ref (None, Shared, Slice u8)];
  [ "lowstar"; "endianness"; "store32_le" ], [Ref (None, Mut, Slice u8); u32];
  [ "lowstar"; "endianness"; "load64_le" ], [Ref (None, Shared, Slice u8)];
  [ "lowstar"; "endianness"; "store64_le" ], [Ref (None, Mut, Slice u8); u64];

  (* LowStar.Endianness, big-endian *)
  [ "lowstar"; "endianness"; "store16_be" ], [Ref (None, Mut, Slice u8); u16];
  [ "lowstar"; "endianness"; "load32_be" ], [Ref (None, Shared, Slice u8)];
  [ "lowstar"; "endianness"; "store32_be" ], [Ref (None, Mut, Slice u8); u32];
  [ "lowstar"; "endianness"; "load64_be" ], [Ref (None, Shared, Slice u8)];
  [ "lowstar"; "endianness"; "store64_be" ], [Ref (None, Mut, Slice u8); u64];
  [ "lowstar"; "endianness"; "load128_be" ], [Ref (None, Shared, Slice u8)];
  [ "lowstar"; "endianness"; "store128_be" ],
    [Ref (None, Mut, Slice u8); Name (["fstar"; "uint128"; "uint128"], [])];

  (* Vec *)
  [ "Vec"; "new" ], [];

  (* Vale assembly functions marked as extern. This should probably be handled earlier *)
  [ "vale"; "stdcalls_x64_sha"; "sha256_update"], [
    Ref (None, Mut, Slice u32); Ref (None, Shared, Slice u8); u32;
    Ref (None, Shared, Slice u32)  
  ];
  [ "vale"; "inline_x64_fadd_inline"; "add_scalar" ], [
    Ref (None, Mut, Slice u64); Ref (None, Shared, Slice u64); Ref (None, Shared, Slice u64)
  ];
  [ "vale"; "stdcalls_x64_fadd"; "add_scalar_e" ], [
    Ref (None, Mut, Slice u64); Ref (None, Shared, Slice u64); Ref (None, Shared, Slice u64)
  ];
  [ "vale"; "inline_x64_fadd_inline"; "fadd" ], [
    Ref (None, Mut, Slice u64); Ref (None, Shared, Slice u64); Ref (None, Shared, Slice u64)
  ];
  [ "vale"; "stdcalls_x64_fadd"; "fadd_e" ], [
    Ref (None, Mut, Slice u64); Ref (None, Shared, Slice u64); Ref (None, Shared, Slice u64)
  ];
  [ "vale"; "inline_x64_fadd_inline"; "fsub" ], [
    Ref (None, Mut, Slice u64); Ref (None, Shared, Slice u64); Ref (None, Shared, Slice u64)
  ];
  [ "vale"; "stdcalls_x64_fsub"; "fsub_e" ], [
    Ref (None, Mut, Slice u64); Ref (None, Shared, Slice u64); Ref (None, Shared, Slice u64)
  ];
  [ "vale"; "inline_x64_fmul_inline"; "fmul" ], [
    Ref (None, Mut, Slice u64); Ref (None, Shared, Slice u64);
    Ref (None, Shared, Slice u64); Ref (None, Mut, Slice u64);
  ];
  [ "vale"; "stdcalls_x64_fmul"; "fmul_e" ], [
    Ref (None, Mut, Slice u64); Ref (None, Shared, Slice u64);
    Ref (None, Shared, Slice u64); Ref (None, Mut, Slice u64);
  ];
  [ "vale"; "inline_x64_fmul_inline"; "fmul2" ], [
    Ref (None, Mut, Slice u64); Ref (None, Shared, Slice u64);
    Ref (None, Shared, Slice u64); Ref (None, Mut, Slice u64);
  ];
  [ "vale"; "stdcalls_x64_fmul"; "fmul2_e" ], [
    Ref (None, Mut, Slice u64); Ref (None, Shared, Slice u64);
    Ref (None, Shared, Slice u64); Ref (None, Mut, Slice u64);
  ];
  [ "vale"; "inline_x64_fmul_inline"; "fmul_scalar" ], [
    Ref (None, Mut, Slice u64); Ref (None, Shared, Slice u64); u64
  ];
  [ "vale"; "stdcalls_x64_fmul"; "fmul_scalar_e" ], [
    Ref (None, Mut, Slice u64); Ref (None, Shared, Slice u64); u64
  ];
  [ "vale"; "inline_x64_fsqr_inline"; "fsqr" ], [
    Ref (None, Mut, Slice u64); Ref (None, Shared, Slice u64); Ref (None, Mut, Slice u64)
  ];
  [ "vale"; "stdcalls_x64_fsqr"; "fsqr_e" ], [
    Ref (None, Mut, Slice u64); Ref (None, Shared, Slice u64); Ref (None, Mut, Slice u64)
  ];
  [ "vale"; "inline_x64_fsqr_inline"; "fsqr2" ], [
    Ref (None, Mut, Slice u64); Ref (None, Shared, Slice u64); Ref (None, Mut, Slice u64)
  ];
  [ "vale"; "stdcalls_x64_fsqr"; "fsqr2_e" ], [
    Ref (None, Mut, Slice u64); Ref (None, Shared, Slice u64); Ref (None, Mut, Slice u64)
  ];
  [ "vale"; "inline_x64_fswap_inline"; "cswap2" ], [
    u64; Ref (None, Mut, Slice u64); Ref (None, Mut, Slice u64)
  ];
  [ "vale"; "stdcalls_x64_fswap"; "cswap2_e" ], [
    u64; Ref (None, Mut, Slice u64); Ref (None, Mut, Slice u64)
  ];

  (* TODO: These functions are recursive, and should be handled properly.
     For now, we hardcode their expected type and mutability in HACL *)
  [ "hacl"; "bignum"; "bn_karatsuba_mul_uint32"], [
      u32; Ref (None, Shared, Slice u32); Ref (None, Shared, Slice u32);
      Ref (None, Mut, Slice u32); Ref (None, Mut, Slice u32)
  ];
  [ "hacl"; "bignum"; "bn_karatsuba_mul_uint64"], [
      u64; Ref (None, Shared, Slice u64); Ref (None, Shared, Slice u64);
      Ref (None, Mut, Slice u64); Ref (None, Mut, Slice u64)
  ];
  [ "hacl"; "bignum"; "bn_karatsuba_sqr_uint32"], [
      u32; Ref (None, Shared, Slice u32);
      Ref (None, Mut, Slice u32); Ref (None, Mut, Slice u32)
  ];
  [ "hacl"; "bignum"; "bn_karatsuba_sqr_uint64"], [
      u64; Ref (None, Shared, Slice u64);
      Ref (None, Mut, Slice u64); Ref (None, Mut, Slice u64)
  ];
    

]

let infer_mut_borrows files =
  (* Map.of_list is only available from OCaml 5.1 onwards *)
  let env = { seen = List.to_seq builtins |> NameMap.of_seq; structs = NameMap.empty } in
  let known = { structs = NameMap.empty; v = VarSet.empty; r = VarSet.empty } in
  let env, files =
    List.fold_left (fun (env, files) (filename, decls) ->
      let env, decls = List.fold_left (fun (env, decls) decl ->
        match decl with
        | Function ({ name; body; return_type; parameters; _ } as f) ->
            (* KPrint.bprintf "[infer-mut] visiting %s\n%a\n" (String.concat "." name)
              PrintMiniRust.pdecl decl; *)
            let atoms, body =
              List.fold_right (fun binder (atoms, e) ->
                let a, e = open_ binder e in
                (* KPrint.bprintf "[infer-mut] opened %s[%s]\n%a\n" binder.name (show_atom_t a) PrintMiniRust.pexpr e; *)
                a :: atoms, e
              ) parameters ([], body)
            in
            (* KPrint.bprintf "[infer-mut] done opening %s\n%a\n" (String.concat "." name)
              PrintMiniRust.pexpr body; *)
            (* Start the analysis with the current state of struct mutability *)
            let known, body = infer env return_type {known with structs = env.structs} body in
            let parameters, body =
              List.fold_left2 (fun (parameters, e) (binder: binding) atom ->
                let e = close atom (Var 0) (lift 1 e) in
                (* KPrint.bprintf "[infer-mut] closed %s[%s]\n%a\n" binder.name (show_atom_t atom) PrintMiniRust.pexpr e; *)
                let mut = want_mut_var atom known in
                let typ = if want_mut_borrow atom known then make_mut_borrow binder.typ else binder.typ in
                { binder with mut; typ } :: parameters, e
              ) ([], body) parameters atoms
            in
            let parameters = List.rev parameters in
            (* We update the environment in two ways. First, we add the function declaration,
               with the mutability of the parameters inferred during the analysis.
               Second, we propagate the information about the mutability of struct fields
               inferred while traversing this function to the global environment. Note, since
               the traversal does not add or remove any bindings, but only increases the
               mutability, we can do a direct replacement instead of a more complex merge *)
            let env = { seen = NameMap.add name (List.map (fun (x: binding) -> x.typ) parameters) env.seen; structs = known.structs } in
            env, Function { f with body; parameters } :: decls
        | Struct ({name; fields; _}) ->
          {env with structs = NameMap.add name fields env.structs}, decl :: decls
        | _ ->
            env, decl :: decls
      ) (env, []) decls in
      let decls = List.rev decls in
      env, (filename, decls) :: files
    ) (env, []) files
  in

  (* We traverse all declarations again, and update the structure decls
     with the new mutability info *)
  List.map (fun (filename, decls) -> filename, List.map (function
    | Struct ({ name; _ } as s) -> Struct { s with fields = NameMap.find name env.structs }
    | x -> x
    ) decls
  ) (List.rev files)

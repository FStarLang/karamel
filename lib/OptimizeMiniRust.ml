(* AstToMiniRust generates code that only uses shared borrows; that is obviously
   incorrect, and so the purpose of this phase is to infer the minimum number of
   variables that need to be marked as `mut`, and the minimum number of borrows
   that need themselves to be `&mut`.

   This improves on an earlier iteration of the compilation scheme where
   everything was marked as mutable by default, a conservative, but suboptimal
   choice.

   We proceed as follows. We carry three sets of variables (all empty initially,
   and all relying on the fact that atoms are globally unique to not have to
   remove entries from those maps when the variables go out of scope):
   - V stands for mutable variables, i.e. the set of variables that need to
     marked as mut using `let mut x = ...`. A variable needs to be marked as mut
     if it is mutably-borrowed, i.e. if `&mut x` occurs.
   - R stands for mutable references, i.e. the set of variables that have type
     `&mut T`.
   - P stands for reference pattern variables -- see comment in EMatch case.
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
open PrintMiniRust

module DataType = struct
  type t = [ `Struct of Name.t | `Variant of Name.t * string ]
  let compare = compare
end

module NameMap = Map.Make(Name)
module DataTypeMap = Map.Make(DataType)
module VarSet = Set.Make(Atom)
module IntSet = Set.Make(Int)

(* Because of (possibly mutual) recursion, we need to express mutability
   inference as a fixed point computation. To each top-level function name, we
   map a property, which is the set of parameters that have to be promoted to
   mutable borrow (mut parameters themselves don't matter -- they're just passed
   by copy and only the function-local copy is mutable). Because parameters may
   or may not have unique names, we identify a function f's parameter with their
   indices. *)
module F = Fix.Fix.ForOrderedType(Name)(Fix.Prop.Set(Set.Make(Int)))

(* The fixed point inference will need to compute unrelated information on the
   go, namely, which struct fields need to become mutable. It is difficult to
   express this as a system of equations, so we simply record those in some
   global state. *)
let structs: (DataType.t, MiniRust.struct_field list) Hashtbl.t =
  Hashtbl.create 31

(* Our environments only contain signatures, and as such, are immutable -- these
   signatures will need to be augmented with information from the valuation to
   get the intended type. *)
type env = {
  signatures: typ list NameMap.t;
}

(* Promote a reference to mutable *)
let make_mut t =
  match t with
  | MiniRust.Ref (l, _, t) ->
      MiniRust.Ref (l, Mut, t)
  | _ ->
      failwith "unexpected: not a ref"

(* Adjust the types of a function's parameters, originally without Mut
   qualifiers, based on what is currently computed in the valuation. *)
let adjust ts mut =
  List.mapi (fun i t ->
    if IntSet.mem i mut then
      make_mut t
    else
      t
  ) ts

(* Convert the mutability qualifiers into a set suitable for fitting as a
   property. *)
let distill ts =
  IntSet.of_list (List.filter_map (fun x -> x) (List.mapi (fun i t ->
    match t with
    | MiniRust.Ref (_, Mut, _) -> Some i
    | _ -> None
  ) ts))

(* Get the type of the arguments of `name`, based on the current state of
   `valuation` *)
let lookup env valuation name =
  (* KPrint.bprintf "lookup: %a\n" PrintMiniRust.pname name; *)
  let ts = NameMap.find name env.signatures in
  adjust ts (valuation name)

let debug env valuation =
  KPrint.bprintf "OptimizeMiniRust -- ENV DEBUG\n";
  NameMap.iter (fun n t ->
    let t = adjust t (valuation n) in
    KPrint.bprintf "%s: %a\n" (String.concat "::" n) ptyps t
  ) env.signatures

(* Now moving on to the local state, for a single function body. *)
type known = {
  v: VarSet.t;
  r: VarSet.t;
  p: VarSet.t;
}

let assert_borrow = function
  | Ref (_, _, t) -> t
  | _ -> failwith "impossible: assert_borrow"

let is_name (t: typ) = match t with Name _ -> true | _ -> false

let assert_name (t: typ option) = match t with
  | Some (Name (n, _)) -> n
  | Some t -> Warn.failwith "impossible: assert_name %a" ptyp t
  | None -> Warn.failwith "impossible: assert_name is None"

let add_mut_var a known =
  (* KPrint.bprintf "%s is let mut\n" (Ast.show_atom_t a); *)
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

let rec make_mut_borrow = function
  | Ref (l, _, t) -> Ref (l, Mut, t)
  | Tuple [Ref (l1, _, t1); Ref (l2, _, t2)] -> Tuple [Ref (l1, Mut, t1); Ref (l2, Mut, t2)]
  | Vec t -> Vec t
  | App (Name (["Box"], []), [_]) as t -> t
  | Array (t, n) -> Array (make_mut_borrow t, n)
  | t ->
      KPrint.bprintf "[make_mut_borrow] %a\n" ptyp t;
      failwith "impossible: make_mut_borrow"

(* Only works for struct types. *)
let add_mut_field (n: DataType.t) f =
  KPrint.bprintf "field %s of type %a is mutable\n" f pdataname n;
  let fields = Hashtbl.find structs n in
  (* Update the mutability of the field element *)
  let fields = List.map (fun (sf: MiniRust.struct_field) ->
    if sf.name = f then {sf with typ = make_mut_borrow sf.typ} else sf) fields in
  Hashtbl.replace structs n fields

let retrieve_pair_type (t: typ) =
  match t with
  | Tuple [e1; e2] -> assert (e1 = e2); e1
  | _ -> failwith "impossible: retrieve_pair_type"


(*  known is the local state, which contains the V, R and P states (see above)

    additionally, this function relies on `valuation` (for the least fixed point
    formulation of this analysis) and mutates `structs` globally *)
let rec infer_expr (env: env) valuation (expected: typ) (known: known) (e: expr): known * expr =
  if Options.debug "rs-mut" then
    KPrint.bprintf "[infer_expr] %a @ %a\n" pexpr e ptyp expected;
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
            let known, e1 = infer_expr env valuation expected known e1 in
            known, Borrow (Mut, Index (e1, r))

        | Index (Open { atom; _ } as e1, e2)  ->
            let known = add_mut_var atom known in
            let known, e2 = infer_expr env valuation Unit known e2 in
            known, Borrow (Mut, Index (e1, e2))

        | Index (Borrow (_, (Open { atom; _ } as e1)), e2)  ->
            let known = add_mut_var atom known in
            let known, e2 = infer_expr env valuation Unit known e2 in
            known, Borrow (Mut, Index (Borrow (Mut, e1), e2))

        | Field (Open _, "0", None)
        | Field (Open _, "1", None) -> failwith "TODO: borrowing slices"

        | Field (Open {atom; _}, _, _) ->
            add_mut_var atom known, Borrow (Mut, e)

        | Field (Deref (Open {atom; _}), _, _) ->
            add_mut_borrow atom known, Borrow (Mut, e)

        | Field (Index (Open {atom; _}, _), _, _) ->
            add_mut_borrow atom known, Borrow (Mut, e)

        | _ ->
            KPrint.bprintf "[infer_expr-mut, borrow] borrwing %a is not supported\n" pexpr e;
            failwith "TODO: borrowing something other than a variable"
      else
        let known, e = infer_expr env valuation (assert_borrow expected) known e in
        known, Borrow (k, e)

  | Open { atom; _ } ->
      (* If we expect this variable to be a mutable borrow, then we remember it and let the caller
         act accordingly. *)
      if is_mut_borrow expected then
        add_mut_borrow atom known, e
      else
        known, e

  | Let (b, e1, e2) ->
      (* KPrint.bprintf "[infer_expr-mut,let] %a\n" pexpr e; *)
      let a, e2 = open_ b e2 in
      (* KPrint.bprintf "[infer_expr-mut,let] opened %s[%s]\n" b.name (show_atom_t a); *)
      let known, e2 = infer_expr env valuation expected known e2 in
      let mut_var = want_mut_var a known in
      let mut_borrow = want_mut_borrow a known in
      KPrint.bprintf "[infer_expr-mut,let-done-e2] %s[%s]: %a let mut ? %b &mut ? %b\n" b.name
        (show_atom_t a)
        ptyp b.typ mut_var mut_borrow;
      let t1 = if mut_borrow then make_mut_borrow b.typ else b.typ in
      let known, e1 = infer_expr env valuation t1 known e1 in
      known, Let ({ b with mut = mut_var; typ = t1 }, e1, close a (Var 0) (lift 1 e2))

  | Call (Name n, targs, es) ->
      if n = ["lowstar";"ignore";"ignore"] then
        (* Since we do not have type-level substitutions in MiniRust, we special-case ignore here.
           Ideally, it would be added to builtins with `Bound 0` as a suitable type for the
           argument. *)
        let known, e = infer_expr env valuation (KList.one targs) known (KList.one es) in
        known, Call (Name n, targs, [ e ])
      else if n = ["Box"; "new"] then
        (* FIXME: we no longer have the type handy so we can't recursively
           descend on KList.one es *)
        known, Call (Name n, targs, es)
      else if n = [ "lib"; "memzero0"; "memzero" ] then
        (* Same as ignore above *)
        let e1, e2 = KList.two es in
        let known, e1 = infer_expr env valuation (Ref (None, Mut, Slice (KList.one targs))) known e1 in
        let known, e2 = infer_expr env valuation u32 known e2 in
        known, Call (Name n, targs, [ e1; e2 ])
      else
        (* TODO: substitute targs in ts -- for now, we assume we don't have a type-polymorphic
           function that gets instantiated with a reference type *)
        let ts = lookup env valuation n in
        let known, es = List.fold_left2 (fun (known, es) e t ->
            let known, e = infer_expr env valuation t known e in
            known, e :: es
          ) (known, []) es ts
        in
        let es = List.rev es in
        known, Call (Name n, targs, es)

  | Call (Operator o, [], _) ->
      (* Most operators are wrapping and were translated to a methodcall.
         We list the few remaining ones here *)
      begin match o with
      | Add | Sub
      | BOr | BAnd | BXor | BNot
      | Eq | Neq | Lt | Lte | Gt | Gte
      | And | Or | Xor | Not -> known, e
      | _ ->
        KPrint.bprintf "[infer_expr-mut,call] %a not supported\n" pexpr e;
        failwith "TODO: operator not supported"
    end

  | Call _ ->
      failwith "TODO: Call"

  (* atom = e3 *)
  | Assign (Open { atom; _ } as e1, e3, t) ->
      (* KPrint.bprintf "[infer_expr-mut,assign] %a\n" pexpr e; *)
      let known, e3 = infer_expr env valuation t known e3 in
      add_mut_var atom known, Assign (e1, e3, t)

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
      (* KPrint.bprintf "[infer_expr-mut,assign] %a\n" pexpr e; *)
      let known = add_mut_borrow atom known in
      let known, e2 = infer_expr env valuation usize known e2 in
      let known, e3 = infer_expr env valuation t known e3 in
      known, Assign (Index (e1, e2), e3, t)

  (* (x.f)[e2] = e3 *)
  | Assign (Index (Field (_, f, st (* optional type *)) as e1, e2), e3, t) ->
      add_mut_field (`Struct (assert_name st)) f;
      let known, e2 = infer_expr env valuation usize known e2 in
      let known, e3 = infer_expr env valuation t known e3 in
      known, Assign (Index (e1, e2), e3, t)

  (* (&atom)[e2] = e3 *)
  | Assign (Index (Borrow (_, (Open { atom; _ } as e1)), e2), e3, t) ->
      (* KPrint.bprintf "[infer_expr-mut,assign] %a\n" pexpr e; *)
      let known = add_mut_var atom known in
      let known, e2 = infer_expr env valuation usize known e2 in
      let known, e3 = infer_expr env valuation t known e3 in
      known, Assign (Index (Borrow (Mut, e1), e2), e3, t)

  | Assign (Field (_, "0", None), _, _)
  | Assign (Field (_, "1", None), _, _) ->
      failwith "TODO: assignment on slice"

  (* (atom[e2]).f = e3 *)
  | Assign (Field (Index ((Open {atom; _} as e1), e2), f, st), e3, t) ->
      let known = add_mut_borrow atom known in
      let known, e2 = infer_expr env valuation usize known e2 in
      let known, e3 = infer_expr env valuation t known e3 in
      known, Assign (Field (Index (e1, e2), f, st), e3, t)

  (* (&n)[e2] = e3 *)
  | Assign (Index (Borrow (_, Name n), e2), e3, t) ->
      (* This case should only occur for globals. For now, we simply mutably borrow it *)
      let known, e2 = infer_expr env valuation usize known e2 in
      let known, e3 = infer_expr env valuation t known e3 in
      known, Assign (Index (Borrow (Mut, Name n), e2), e3, t)

  (* (&(&atom)[e2])[e3] = e4 *)
  | Assign (Index (Borrow (_, Index (Borrow (_, (Open {atom; _} as e1)), e2)), e3), e4, t) ->
      let known = add_mut_var atom known in
      let known, e2 = infer_expr env valuation usize known e2 in
      let known, e3 = infer_expr env valuation usize known e3 in
      let known, e4 = infer_expr env valuation t known e4 in
      known, Assign (Index (Borrow (Mut, Index (Borrow (Mut, e1), e2)), e3), e4, t)

  (* (&(atom.f))[e1] = e2 *)
  | Assign (Index (Borrow (_, Field (Open {atom; _} as e1, f, t)), e2), e3, t1) ->
      let known = add_mut_var atom known in
      let known, e2 = infer_expr env valuation usize known e2 in
      let known, e3 = infer_expr env valuation usize known e3 in
      known, Assign (Index (Borrow (Mut, Field (e1, f, t)), e2), e3, t1)

  | Assign _ ->
      KPrint.bprintf "[infer_expr-mut,assign] %a unsupported %s\n" pexpr e (show_expr e);
      failwith "TODO: unknown assignment"

  | AssignOp _ -> failwith "AssignOp nodes should only be introduced after mutability infer_exprence"
  | Var _
  | VecNew _
  | Name _
  | Constant _
  | ConstantString _
  | Unit
  | Panic _
  | Operator _ ->
      known, e

  | Array (List es) as e0 ->
      (* FIXME: we are sometimes recursively called with not enough type
         information from the copy_from_slice case, below *)
      if expected <> Unit then
        let t_elt = match expected with Slice t | Array (t, _) -> t | _ -> failwith (KPrint.bsprintf "impossible: %a" ptyp expected) in
        let known, es = List.fold_left (fun (known, es) e ->
          let known, e = infer_expr env valuation t_elt known e in
          known, e :: es
        ) (known, []) es in
        let es = List.rev es in
        known, Array (List es)
      else
        known, e0

  | Array (Repeat (e, n)) as e0 ->
      (* FIXME: we are sometimes recursively called with not enough type
         information from the copy_from_slice case, below *)
      if expected <> Unit then
        let t_elt = match expected with Slice t | Array (t, _) -> t | _ -> failwith (KPrint.bsprintf "impossible: %a" ptyp expected) in
        let known, e = infer_expr env valuation t_elt known e in
        known, Array (Repeat (e, n))
      else
        known, e0

  | IfThenElse (e1, e2, e3) ->
      let known, e1 = infer_expr env valuation bool known e1 in
      let known, e2 = infer_expr env valuation expected known e2 in
      let known, e3 =
        match e3 with
        | Some e3 ->
            let known, e3 = infer_expr env valuation expected known e3 in
            known, Some e3
        | None ->
            known, None
      in
      known, IfThenElse (e1, e2, e3)

  | As (e, t) ->
      (* Not really correct, but As is only used for integer casts *)
      let known, e = infer_expr env valuation t known e in
      known, As (e, t)

  | For (b, e1, e2) ->
      let known, e2 = infer_expr env valuation Unit known e2 in
      known, For (b, e1, e2)

  | While (e1, e2) ->
      let known, e2 = infer_expr env valuation Unit known e2 in
      known, While (e1, e2)

  | MethodCall (e1, m, e2) ->
      (* There are only a few instances of these generated by AstToMiniRust, so we just review them
         all here. Note that there are two possible strategies: AstToMiniRust could use an IndexMut
         AST node to indicate e.g. that the destination of `copy_from_slice` ought to be mutable, or
         we just bake that knowledge in right here. *)
      begin match m with
      | [ "wrapping_add" | "wrapping_div" | "wrapping_mul"
      |   "wrapping_neg" | "wrapping_rem" | "wrapping_shl"
      |   "wrapping_shr" | "wrapping_sub"
      |   "to_vec" | "into_boxed_slice" | "into" | "len" ] ->
          known, MethodCall (e1, m, e2)
      | ["split_at"] ->
          assert (List.length e2 = 1);
          let known, e2 = infer_expr env valuation usize known (List.hd e2) in
          let t1 = retrieve_pair_type expected in
          let known, e1 = infer_expr env valuation t1 known e1 in
          if is_mut_borrow expected then
            known, MethodCall (e1, ["split_at_mut"], [e2])
          else
            known, MethodCall (e1, m, [e2])
      | ["copy_from_slice"] ->
          assert (List.length e2 = 1);
          begin match e1 with
          | Index (dst, range) ->
              (* We do not have access to the types of e1 and e2. However, the concrete
                 type should not matter during mut infer_exprence, we thus use Unit as a default *)
              let known, dst = infer_expr env valuation (Ref (None, Mut, Unit)) known dst in
              let known, e2 = infer_expr env valuation (Ref (None, Shared, Unit)) known (List.hd e2) in
              known, MethodCall (Index (dst, range), m, [e2])
          | _ ->
              (* The other form stems from Pulse.Lib.Slice which, here, puts an
                  actual slice on the left-hand side. *)
              let e2 = KList.one e2 in
              let known, e1 = infer_expr env valuation (Ref (None, Mut, Slice Unit)) known e1 in
              let known, e2 = infer_expr env valuation (Ref (None, Mut, Slice Unit)) known e2 in
              known, MethodCall (e1, m, [e2])
          end
      | [ "push" ] -> begin match e1 with
          | Open {atom; _} -> add_mut_var atom known, MethodCall (e1, m, e2)
          | _ -> failwith "TODO: push on complex expressions"
          end
      | _ ->
          KPrint.bprintf "%a unsupported\n" pexpr e;
          failwith "TODO: MethodCall"
      end

  | Range (e1, e2, b) ->
      known, Range (e1, e2, b)

  | Struct (name, es) ->
      KPrint.bprintf "%a\n" pdataname name;
      (* The declaration of the struct should have been traversed beforehand, hence
         it should be in the map *)
      let fields_mut = Hashtbl.find structs name in
      let known, es = List.fold_left2 (fun (known, es) (fn, e) (f: struct_field) ->
        assert (fn = f.name);
        let known, e = infer_expr env valuation f.typ known e in
        known, (fn, e) :: es
      ) (known, []) es fields_mut in
      let es = List.rev es in
      known, Struct (name, es)

  | Match (e_scrut, t, arms) as _e_match ->
      (* We have the expected type of the scrutinee: valuation *)
      let known, e = infer_expr env valuation t known e_scrut in
      let known, arms = List.fold_left_map (fun known ((bs, _, _) as branch) ->
        let atoms, pat, e = open_branch branch in
        let known, e = infer_expr env valuation expected known e in
        (* Given a pattern p of type t, and a known map:
          i.  if the pattern contains f = x *and* x is in R, then the field f of
              the struct type (provided by the context t) needs to be mutable --
              this is the same as when we see x.f[0] = 1 -- field f needs to be
              mutable (but not x!)
          ii. if the pattern contains f = x *and* x is a /mutable/ borrow, then this is
              going to be a move-out -- this is not the same behavior as a
              let-binding. Since borrows do not implement Copy, we need to do
              some extra work. Consider this example:

              let mut a = [ 0; 32 ];
              // This works (is x borrowed automatically?)
              let f: Foo = Foo { x: &mut a };
              f.x[0] = 1;
              assert_eq!(f.x[0], 1);
              // This doesn't (x is moved out of g and not put back in)
              let g: Foo = Foo { x: &mut a };
              match g {
                  Foo { x } => {
                    x[0] += 1;
                    // Assert fails to type-check because g.x is moved out
                    assert_eq!(g.x[0], 2);
                  }
              };
              assert_eq!(a[0], 2);

              this example can be fixed using a ref mut pattern (is this what
              happens with field projection under the hood?):

              let mut g: Foo = Foo { x: &mut a };
              match g {
                  Foo { ref mut x } => {
                    x[0] += 1;
                    // Lifetime of `x` ends, `g` becomes available again, but
                    // `x` has type double-borrow!
                    assert_eq!(g.x[0], 2);
                  }
              };
              assert_eq!(a[0], 2);

              So we need to do two things: ii.a. mark the field as a ref mut
              pattern, and ii.b. mark the variable itself as mutable...
        *)
        let rec update_fields (known: known) pat: known * pat =
          match pat with
          | StructP (name as struct_name, fieldpats) ->
              let fields = Hashtbl.find structs name in
              let known, fieldpats = List.fold_left2 (fun (known, fieldpats) (f, pat) { name; typ; _ } ->
                assert (f = name);
                match pat with
                | OpenP open_var ->
                    let { atom; _ } = open_var in
                    let mut = VarSet.mem atom known.r in
                    let ref = match typ with
                      | App (Name (["Box"], []), [_]) | Vec _ | Ref (_, Mut, _) ->
                          true (* prevent a move-out, again *)
                      | _ ->
                          mut (* something mutated relying on an implicit conversion to ref *)
                    in
                    (* KPrint.bprintf "In match:\n%a\nPattern variable %s: mut=%b, ref=%b\n" *)
                    (*   pexpr e_match open_var.name mut ref; *)
                    (* i., above *)
                    if mut then add_mut_field struct_name f;
                    (* ii.b. *)
                    let known = match e_scrut with
                      | Open { atom; _ } when mut -> add_mut_var atom known
                      | Deref (Open { atom; _ }) when mut -> add_mut_borrow atom known
                      | _ ->
                          (* KPrint.bprintf "%a is not open or deref\n" pexpr e; *)
                          known
                    in
                    (* ii.a *)
                    let known = if ref then { known with p = VarSet.add atom known.p } else known in
                    known, (f, OpenP open_var) :: fieldpats
                | _ ->
                    let known, pat = update_fields known pat in
                    known, (f, pat) :: fieldpats
              ) (known, []) fieldpats fields in
              let fieldpats = List.rev fieldpats in
              known, StructP (name, fieldpats)

          | TupleP ps ->
              let known, ps = List.fold_left (fun (known, ps) p ->
                let known, p = update_fields known p in
                known, p :: ps
              ) (known, []) ps in
              known, TupleP (List.rev ps)

          | Wildcard | Literal _ -> known, pat
          | OpenP _ -> known, pat (* no such thing as mutable struct fields or variables in Low* *)
          |  _ -> Warn.failwith "TODO: Match %a" ppat pat
        in
        let known, pat = update_fields known pat in
        let bs = List.map2 (fun a b ->
          let ref = VarSet.mem a known.p in
          let mut = VarSet.mem a known.r in
          { b with ref; mut }
        ) atoms bs in
        let branch = close_branch atoms (bs, pat, e) in
        known, branch
      ) known arms in
      known, Match (e, t, arms)

  | Index (e1, e2) ->
      (* The cases where we perform an assignment on an index should be caught
         earlier. This should therefore only occur when accessing a variable
         in an array *)
      let expected = Ref (None, Shared, expected) in
      let known, e1 = infer_expr env valuation expected known e1 in
      let known, e2 = infer_expr env valuation usize known e2 in
      known, Index (e1, e2)

  (* Special case for array slices. This occurs, e.g., when calling a function with
     a struct field *)
  | Field (Open { atom; name }, "0", None) | Field (Open { atom; name }, "1", None) ->
      KPrint.bprintf "%s!!!\n" name;
      if is_mut_borrow expected then
        add_mut_borrow atom known, e
      else
        known, e

  | Field (_, f, t) ->
      if is_mut_borrow expected then
        add_mut_field (`Struct (assert_name t)) f;
      known, e

  | Deref _ ->
      known, e

  | Tuple es ->
      let t_elt = match expected with Tuple t -> t | _ -> failwith "impossible" in
      let known, es = List.fold_left2 (fun (known, es) e t ->
        let known, e = infer_expr env valuation t known e in
        known, e :: es
      ) (known, []) es t_elt in
      known, Tuple (List.rev es)


let empty: known = { v = VarSet.empty; r = VarSet.empty; p = VarSet.empty }

let infer_function (env: env) valuation (d: decl): decl =
  match d with
  | Function ({ name; body; return_type; parameters; _ } as f) ->
      if Options.debug "rs-mut" then
        KPrint.bprintf "[infer-mut] visiting %s\n" (String.concat "::" name);
      let atoms, body =
        List.fold_right (fun binder (atoms, e) ->
          let a, e = open_ binder e in
          (* KPrint.bprintf "[infer-mut] opened %s[%s]\n%a\n" binder.name (show_atom_t a) pexpr e; *)
          a :: atoms, e
        ) parameters ([], body)
      in
      (* KPrint.bprintf "[infer-mut] done opening %s\n%a\n" (String.concat "." name)
        pexpr body; *)
      (* Start the analysis with the current state of struct mutability *)
      let known, body = infer_expr env valuation return_type empty body in
      let parameters, body =
        List.fold_left2 (fun (parameters, e) (binder: binding) atom ->
          let e = close atom (Var 0) (lift 1 e) in
          (* KPrint.bprintf "[infer-mut] closed %s[%s]\n%a\n" binder.name (show_atom_t atom) pexpr e; *)
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
      Function { f with body; parameters }
  | _ ->
      assert false

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
]

let infer_mut_borrows files =
  (* Fill the `structs` global table with initial field information. Some of
     these fields will be promoted to "mutable" as a side-effect of the
     mutability inference. *)
  List.iter (fun (_, decls) ->
    List.iter (fun decl ->
      match decl with
      | Struct ({name; fields; _}) ->
          Hashtbl.add structs (`Struct name) fields
      | Enumeration { name; items; _ } ->
          List.iter (fun (cons, fields) ->
            Option.value fields ~default:[] |>
            Hashtbl.add structs (`Variant (name, cons))
          ) items
      | _ ->
          ()
    ) decls
  ) files;

  (* When inside a function body, we only care about the type of the parameters. *)
  let env = {
    signatures = NameMap.of_seq (List.to_seq (builtins @
      List.concat_map (fun (_, decls) ->
        List.filter_map (function
          | Function { parameters; name; _ } ->
              Some (name, List.map (fun (p: MiniRust.binding) -> p.typ) parameters)
          | _ ->
              None
        ) decls) files))
  } in

  (* But for the fixed point computation, we need complete definitions for each
     name, in order to implement rhs. *)
  let definitions = List.fold_left (fun map (_, decls) ->
    List.fold_left (fun map decl -> NameMap.add (name_of_decl decl) decl map) map decls
  ) NameMap.empty files in

  let builtins = NameMap.of_seq (List.to_seq builtins) in

  (* Given `name`, and given sets of mutable parameters for other definitions in
    `valuation`, compute which of the parameters in this function need to be
    mutable borrows. *)
  let rhs name valuation =
    if NameMap.mem name builtins then
      (* No computation needed for builtins, the information is readily available *)
      distill (NameMap.find name builtins)
    else
      match infer_function env valuation (NameMap.find name definitions) with
      | Function { parameters; _ } -> distill (List.map (fun (b: MiniRust.binding) -> b.typ) parameters)
      | _ -> failwith "impossible"
  in

  let valuation = F.lfp rhs in

  (* lfp does not actually perform any computation.
    We now apply the valuation to all functions to compute mutability inference. *)
  let files = List.map (fun (filename, decls) -> filename, List.map (function
    | Function _ as decl ->
        infer_function env valuation decl
    | x -> x
    ) decls
  ) (List.rev files) in

  (* We can finally update the struct and enumeration fields mutability
     based on the information computed during inference on functions *)
  List.map (fun (filename, decls) -> filename, List.map (function
    | Struct ({ name; _ } as s) -> Struct { s with fields = Hashtbl.find structs (`Struct name) }
    | Enumeration s  ->
        Enumeration { s with items = List.map (fun (cons, fields) ->
          cons, match fields with
            | None -> None
            | Some _ -> Some (Hashtbl.find structs (`Variant (s.name, cons)))
        ) s.items }
    | x -> x
    ) decls
  ) (List.rev files)


(* Transformations occuring on the MiniRust AST, after translation and mutability inference *)

(* Loop unrolling introduces an implicit binder that does not interact well
   with the substitutions occurring in mutability inference.
   We perform it after the translation *)
let unroll_loops = object
  inherit [_] map_expr as super
  method! visit_For _ b e1 e2 =
    let e2 = super#visit_expr () e2 in

    match e1 with
    | Range (Some (Constant (UInt32, init as k_init) as e_init), Some (Constant (UInt32, max)), false)
      when (
        let init = int_of_string init in
        let max = int_of_string max in
        let n_loops = max - init in
        n_loops <= !Options.unroll_loops
      ) ->
        let init = int_of_string init in
        let max = int_of_string max in
        let n_loops = max - init in

        if n_loops = 0 then Unit

        else if n_loops = 1 then subst e_init 0 e2

        else Call (Name ["krml"; "unroll_for!"], [], [
          Constant (CInt, string_of_int n_loops);
          ConstantString b.name;
          Constant k_init;
          Constant (UInt32, "1");
          e2
        ])

    | _ -> For (b, e1, e2)
end

let remove_trailing_unit = object
  inherit [_] map_expr as super
  method! visit_Let _ b e1 e2 =
    let e1 = super#visit_expr () e1 in
    let e2 = super#visit_expr () e2 in
    match e2 with
    | Unit -> e1
    | _ -> Let (b, e1, e2)
end

(* The Rust compiler will automatically insert borrows or dereferences
   when required for methodcalls and field accesses *)
let remove_auto_deref = object
  inherit [_] map_expr as super
  method! visit_MethodCall _ e1 n e2 =
    let e1 = super#visit_expr () e1 in
    let e2 = List.map (super#visit_expr ()) e2 in
    match e1 with
    | Borrow (_, e) | Deref e -> MethodCall (e, n, e2)
    | _ -> MethodCall (e1, n, e2)

  method! visit_Field _ e n t =
    let e = super#visit_expr () e in
    match e with
    | Deref e -> Field (e, n, t)
    | _ -> Field (e, n, t)
end

(* Rewrite eligible terms with the assign-op pattern.
   Ex: x = x & y becomes x &= y *)
let rewrite_assign_op = object
  inherit [_] map_expr as super
  method! visit_Assign _ e1 e2 t =
    let e1 = super#visit_expr () e1 in
    let e2 = super#visit_expr () e2 in
    match e2 with
    | Call (Operator o, ts, [ e_l; e_r ]) when e1 = e_l ->
        assert (ts = []);
        AssignOp (e1, o, e_r, t)
    | _ -> Assign (e1, e2, t)
end

(* Rewrite boolean expressions that are the negation of a condition *)
let rewrite_nonminimal_bool = object
  inherit [_] map_expr as super
  method! visit_Call _ e tys args =
    let e = super#visit_expr () e in
    let args = List.map (super#visit_expr ()) args in
    match e, tys, args with
    | Operator Not, [], [ Call (Operator o, [], [e1; e2]) ] when Constant.is_comp_op o ->
        Call (Operator (Constant.comp_neg o), [], [e1; e2])
    | _ -> Call (e, tys, args)
end

let remove_deref_addrof = object
  inherit [_] map_expr as super
  method! visit_Deref _ e =
    let e = super#visit_expr () e in
    match e with
    | Borrow (_, e) -> e
    | _ -> Deref e
end

let map_funs f_map files =
  let files =
    List.fold_left (fun files (filename, decls) ->
      let decls = List.fold_left (fun decls decl ->
        match decl with
        | Function ({ body; _ } as f) ->
            let body = f_map () body in
            Function {f with body} :: decls
        | _ -> decl :: decls
      ) [] decls in
      let decls = List.rev decls in
      (filename, decls) :: files
    ) [] files
  in
  List.rev files

let simplify_minirust files =
  let files = map_funs unroll_loops#visit_expr files in
  let files = map_funs remove_auto_deref#visit_expr files in
  let files = map_funs rewrite_assign_op#visit_expr files in
  let files = map_funs rewrite_nonminimal_bool#visit_expr files in
  let files = map_funs remove_deref_addrof#visit_expr files in
  (* We do this simplification last, as the previous passes might
     have introduced unit statements *)
  let files = map_funs remove_trailing_unit#visit_expr files in
  files

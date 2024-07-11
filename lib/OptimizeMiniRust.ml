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
  { known with v = VarSet.add a known.v }

let add_mut_borrow a known =
  KPrint.bprintf "%s is &mut\n" (Ast.show_atom_t a);
  { known with r = VarSet.add a known.r }

let want_mut_var a known =
  KPrint.bprintf "%s is let mut\n" (Ast.show_atom_t a);
  VarSet.mem a known.v

let want_mut_borrow a known =
  VarSet.mem a known.r

let is_mut_borrow = function
  | Ref (_, Mut, _) -> true
  | _ -> false

let make_mut_borrow = function
  | Ref (l, _, t) -> Ref (l, Mut, t)
  | _ -> failwith "impossible: make_mut_borrow"

let assert_borrow = function
  | Ref (_, _, t) -> t
  | _ -> failwith "impossible: assert_borrow"

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
      let a, e2 = open_ b e2 in
      let known, e2 = infer env expected known e2 in
      let mut_var = want_mut_var a known in
      let mut_borrow = want_mut_borrow a known in
      KPrint.bprintf "[infer-mut,let] %s[%s]: %a let mut ? %b &mut ? %b\n" b.name
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
      else
        failwith "TODO: recursion"

  | Call _ ->
      failwith "TODO: Call"

  | Assign (Open { atom; _ }, e3, t) ->
      KPrint.bprintf "[infer-mut,assign] %a\n" PrintMiniRust.pexpr e;
      let known, e3 = infer env t known e3 in
      add_mut_var atom known, e3

  | Assign (Index (Open { atom; _ } as e1, e2), e3, t) ->
      KPrint.bprintf "[infer-mut,assign] %a\n" PrintMiniRust.pexpr e;
      let known = add_mut_borrow atom known in
      let known, e2 = infer env usize known e2 in
      let known, e3 = infer env t known e3 in
      known, Assign (Index (e1, e2), e3, t)

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

  | MethodCall _ ->
      failwith "TODO: MethodCall"

  | Range (e1, e2, b) ->
      known, Range (e1, e2, b)

  | Struct _ ->
      failwith "TODO: Struct"

  | Match _ ->
      failwith "TODO: Match"

  | Index _ ->
      failwith "TODO: Index"

  | Field _ ->
      failwith "TODO: Field"

  | Deref _ ->
      failwith "TODO: Deref"

let infer_mut_borrows files =
  let env = { seen = NameMap.empty } in
  let known = { v = VarSet.empty; r = VarSet.empty } in
  let _, files =
    List.fold_left (fun (env, files) (filename, decls) ->
      let env, decls = List.fold_left (fun (env, decls) decl ->
        match decl with
        | Function ({ name; body; return_type; parameters; _ } as f) ->
            KPrint.bprintf "[infer-mut] visiting %s\n%a\n" (String.concat "." name)
              PrintMiniRust.pexpr body;
            let atoms, body =
              List.fold_right (fun binder (atoms, e) ->
                let a, e = open_ binder e in
                a :: atoms, e
              ) parameters ([], body)
            in
            let known, body = infer env return_type known body in
            let parameters, body =
              List.fold_right2 (fun (binder: binding) atom (parameters, e) ->
                let e = close atom (Var 0) (lift 1 e) in
                let mut = want_mut_var atom known in
                let typ = if want_mut_borrow atom known then make_mut_borrow binder.typ else binder.typ in
                { binder with mut; typ } :: parameters, e
              ) parameters atoms ([], body)
            in
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

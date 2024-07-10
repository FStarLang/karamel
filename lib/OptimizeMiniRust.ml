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
  { known with v = VarSet.add a v }

let add_mut_borrow a known =
  { known with r = VarSet.add a r }

let want_mut_var a known =
  VarSet.mem a known.v

let want_mut_borrow a known =
  VarSet.mem a known.r

let is_mut_borrow = function
  | Borrow (Mut, _) -> true
  | _ -> false

let make_mut_borrow = function
  | Borrow (_, t) -> Borrow (Mut, t)
  | _ -> failwith "impossible: make_mut_borrow"

let assert_borrow = function
  | Borrow (_, t) -> t
  | _ -> failwith "impossible: assert_borrow"

let rec infer (env: env) (expected: typ) (known: known) (e: expr): known * expr =
  match expr with
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

  | Open { atom; _ } ->
      (* If we expect this variable to be a mutable borrow, then we remember it and let the caller
         act accordingly. *)
      if need = MakeMut then
        add_mut_borrow atom known, expr
      else
        expr

  | Let (b, e1, e2) ->
      let a, e2 = open_ b e2 in
      let known, e2 = infer env need known e2 in
      let mut = want_mut_var a known in
      let t1 = if want_mut_borrow a known then make_mut_borrow b.typ else b.typ in
      let known, e1 = infer env typ e1 in
      known, Let ({ b with mut; typ = t1 }, e1, close a (Var 0) e2)

  | Call (Name n, targs, es) ->
      if NameMap.mem env.seen n then
        let ts = NameMap.find env.seen n in
        let known, es = List.fold_left (fun (known, es) e ->
          let known, e = 


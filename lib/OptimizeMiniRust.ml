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

   Finally, the transformation receives a mode as an input parameter; if the
   mode is Mut, then the subexpression being visited (e.g. &x) needs to return a
   mutable borrow, meaning it gets rewritten (e.g. into &mut x) and the set V
   increases (because the Rust rule is that you can only write `&mut x` if `x`
   itself is declared with `let mut`).
*)

let rec infer_mut_borrows = false

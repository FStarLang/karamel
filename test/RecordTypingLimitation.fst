module RecordTypingLimitation

(* Some notes to self to remember why this is a bug and what can be done to fix
 * it. This situation was initially found by trying to enable
 * inline_for_extraction for all projectors. What happens is:
 * - we monomorphize functions, not data types
 * - then we type-check the application which contains a match followed by a
 *   projection
 * - the projection's scrutinee is a polymorphic data type (here, a [t Int32.t])
 *   for which Checker.ml (at line 817) doesn't know what to say, since, it only
 *   expects a monomorphic instance.
 *
 * Proposed fix: replicate the logic in args_of_branch to PRecord. *)

type t (a: Type0) = {
  x: a;
  y: Int32.t;
}

inline_for_extraction
let proj #a (x: t a): a = match x with
  | { x } -> x

let g: t Int32.t = { x = 0l; y = 0l }

let f x = x

let main () =
  let x = f (proj g) in
  x

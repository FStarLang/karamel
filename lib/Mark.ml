(* See comments in UseAnalysis.ml *)

(* Whether the variable may occur, post-C preprocessor, in the generated code. *)
type occurrence = MaybeAbsent | Present
  [@@deriving show]

(* How many times this variable will end up being used, at runtime. *)
type usage = AtMost of int
  [@@deriving show]

let is_atmost k (AtMost n) = n <= k

let default = MaybeAbsent, AtMost max_int

module WildCard

open FStar.HyperStack.ST

type t = | A | B

(* These should all be compiled as switches. *)
let int_of_t (x: t): Stack Int32.t (fun _ -> true) (fun _ _ _ -> true) =
  match x with
  | A -> 0l
  | _ -> 0l

let main () =
  match int_of_t B with
  | 0l -> 0l
  | 1l -> 0l
  | _ -> 0l

(** This module provides various substitution functions. *)

(* ---------------------------------------------------------------------------- *)

open Ast

(* Counting binders. *)

class map_counting = object
  (* The environment [i] has type [int]. *)
  inherit [int] map
  (* The environment [i] keeps track of how many binders have been
     entered. It is incremented at each binder. *)
  method extend i (_ : binder) =
    i + 1
end

(* ---------------------------------------------------------------------------- *)

(* Lifting. *)

class lift (k : int) = object
  inherit map_counting
  (* A local variable (one that is less than [i]) is unaffected;
     a free variable is lifted up by [k]. *)
  method tybound i j =
    if j < i then
      EBound j
    else
      EBound (j + k)
end

let lift (k : int) (expr : expr) : expr =
  if k = 0 then
    expr
  else
    (new lift k) # visit 0 expr


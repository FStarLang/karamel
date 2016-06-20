(** This module provides various substitution functions. *)

(* ---------------------------------------------------------------------------- *)

open Ast

(* Counting binders. *)

class map_counting = object
  (* The environment [i] has type [int]. *)
  inherit [int] map
  (* The environment [i] keeps track of how many binders have been
     entered. It is incremented at each binder. *)
  method extend i (_: binder) =
    i + 1
end

(* ---------------------------------------------------------------------------- *)

(* Lifting. *)

class lift (k: int) = object
  inherit map_counting
  (* A local variable (one that is less than [i]) is unaffected;
     a free variable is lifted up by [k]. *)
  method tybound i j =
    if j < i then
      EBound j
    else
      EBound (j + k)
end

let lift (k: int) (expr: expr): expr =
  if k = 0 then
    expr
  else
    (new lift k) # visit 0 expr

(* ---------------------------------------------------------------------------- *)

(* Substitute [e2] for [i] in [e1]. *)

class subst (e2: expr) = object
  (* The environment [i] is the variable that we are looking for. *)
  inherit map_counting
  (* The target variable [i] is replaced with [t2]. Any other
     variable is unaffected. *)
  method ebound i j =
    if j = i then
      lift i e2
    else
      EBound (if j < i then j else j-1)
end

let subst (e2: expr) (i: int) (e1: expr) =
  (new subst e2) # visit i e1

(* ---------------------------------------------------------------------------- *)

(* Close [binder] into bound variable i *)

class close (binder: binder) = object
  inherit map_counting

  method eopen i b =
    if b == binder then
      EBound i
    else
      EOpen b
end

let close (b: binder) (i: int) (e: expr) =
  (new close b) # visit i e

let close_binder b e =
  close b 0 e

(* ---------------------------------------------------------------------------- *)

let open_binder b e1 =
  subst (EOpen b) 0 e1

let open_function_binders =
  List.fold_right open_binder

let close_function_binders bs e1 =
  let rec close_binderi i e1 = function
    | b :: bs -> close_binderi (i + 1) (close b i e1) bs
    | [] -> e1
  in
  close_binderi 0 e1 (List.rev bs)

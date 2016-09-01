(** This module provides various substitution functions. *)

(* ---------------------------------------------------------------------------- *)

open Ast

(* Counting binders. *)

class map_counting = object
  (* The environment [i] has type [int]. *)
  inherit [int] map
  (* The environment [i] keeps track of how many binders have been
     entered. It is incremented at each binder. *)
  method! extend i (_: binder) =
    i + 1
end

(* ---------------------------------------------------------------------------- *)

(* Lifting. *)

class lift (k: int) = object
  inherit map_counting
  (* A local variable (one that is less than [i]) is unaffected;
     a free variable is lifted up by [k]. *)
  method! ebound i _ j =
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
  method! ebound i _ j =
    if j = i then
      (lift i e2).node
    else
      EBound (if j < i then j else j-1)
end

let subst (e2: expr) (i: int) (e1: expr) =
  (new subst e2) # visit i e1

(* ---------------------------------------------------------------------------- *)

(* Close [binder] into bound variable i *)

class close (atom': Atom.t) = object
  inherit map_counting

  method! eopen i _ name atom =
    if Atom.equal atom atom' then
      EBound i
    else
      EOpen (name, atom)
end

let close (a: Atom.t) (i: int) (e: expr) =
  (new close a) # visit i e

let close_binder b e =
  close b.atom 0 e

(* ---------------------------------------------------------------------------- *)

let open_binder b e1 =
  let a = Atom.fresh () in
  let b = { b with atom = a } in
  b, subst { node = EOpen (b.name, a); mtyp = b.typ } 0 e1

let open_function_binders binders term =
  List.fold_right (fun binder (acc, term) ->
    let binder, term = open_binder binder term in
    binder :: acc, term
  ) binders ([], term)

let close_function_binders bs e1 =
  let rec close_binderi i e1 = function
    | b :: bs -> close_binderi (i + 1) (close b.atom i e1) bs
    | [] -> e1
  in
  close_binderi 0 e1 (List.rev bs)

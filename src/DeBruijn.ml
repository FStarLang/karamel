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

class map_t_counting = object
  (* The environment [i] has type [int]. *)
  inherit [int] map
  (* The environment [i] keeps track of how many binders have been
     entered. It is incremented at each binder. *)
  method! extend_t i =
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
    (new lift k)#visit 0 expr

class lift_t (k: int) = object
  inherit map_t_counting
  method! tbound i j =
    if j < i then
      TBound j
    else
      TBound (j + k)
end

let lift_t (k: int) (typ: typ): typ =
  if k = 0 then
    typ
  else
    (new lift_t k)#visit_t 0 typ

class lift_p (k: int) = object
  inherit map_counting
  method! pbound i _ j =
    if j < i then
      PBound j
    else
      PBound (j + k)
end

let lift_p (k: int) (pat: pattern): pattern =
  if k = 0 then
    pat
  else
    (new lift_p k)#visit_pattern 0 pat

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
  (new subst e2)#visit i e1

let subst_n e es =
  let l = List.length es in
  KList.fold_lefti (fun i body arg ->
    let k = l - i - 1 in
    subst arg k body
  ) e es

(* Substitute [t2] for [i] in [t1]. *)

class subst_t (t2: typ) = object
  (* The environment [i] is the variable that we are looking for. *)
  inherit map_t_counting
  (* The target variable [i] is replaced with [t2]. Any other
     variable is unaffected. *)
  method! tbound i j =
    if j = i then
      lift_t i t2
    else
      TBound (if j < i then j else j-1)
end

let subst_t (t2: typ) (i: int) (t1: typ) =
  (new subst_t t2)#visit_t i t1

let subst_tn t ts =
  let l = List.length ts in
  KList.fold_lefti (fun i body arg ->
    let k = l - i - 1 in
    subst_t arg k body
  ) t ts

class subst_p (p2: pattern) = object
  (* The environment [i] is the variable that we are looking for. *)
  inherit map_counting
  (* The target variable [i] is replaced with [t2]. Any other
     variable is unaffected. *)
  method! pbound i _ j =
    if j = i then
      (lift_p i p2).node
    else
      PBound (if j < i then j else j-1)
end

let subst_p (p2: pattern) (i: int) (p1: pattern) =
  (new subst_p p2)#visit_pattern i p1

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
  (new close a)#visit i e

let close_binder b e =
  close b.node.atom 0 e

(* ---------------------------------------------------------------------------- *)

let open_binder b e1 =
  let a = Atom.fresh () in
  let b = { b with node = { b.node with atom = a } } in
  b, subst { node = EOpen (b.node.name, a); typ = b.typ } 0 e1

let open_binders binders term =
  List.fold_right (fun binder (acc, term) ->
    let binder, term = open_binder binder term in
    binder :: acc, term
  ) binders ([], term)

let open_branch bs pat expr =
  List.fold_right (fun binder (bs, pat, expr) ->
    let b, expr = open_binder binder expr in
    let pat =
      subst_p { node = POpen (b.node.name, b.node.atom); typ = b.typ } 0 pat
    in
    b :: bs, pat, expr
  ) bs ([], pat, expr)

let close_binders bs e1 =
  let rec close_binderi i e1 = function
    | b :: bs -> close_binderi (i + 1) (close b.node.atom i e1) bs
    | [] -> e1
  in
  close_binderi 0 e1 (List.rev bs)

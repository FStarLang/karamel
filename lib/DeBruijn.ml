(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 License. *)

(** This module provides various substitution functions. *)

(* ---------------------------------------------------------------------------- *)

open Ast

(* Counting binders. *)

class map_counting = object
  (* The environment [i] has type [int]. *)
  inherit [_] map
  (* The environment [i] keeps track of how many binders have been
     entered. It is incremented at each binder. *)
  method! extend i (_: binder) =
    i + 1
end

class map_t_counting = object
  (* The environment [i] has type [int]. *)
  inherit [_] map
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
  method! visit_EBound (i, _) j =
    if j < i then
      EBound j
    else
      EBound (j + k)
end

let lift (k: int) (expr: expr): expr =
  if k = 0 then
    expr
  else
    (new lift k)#visit_expr_w 0 expr

class lift_t (k: int) = object
  inherit map_t_counting
  method! visit_TBound i j =
    if j < i then
      TBound j
    else
      TBound (j + k)
end

let lift_t (k: int) (typ: typ): typ =
  if k = 0 then
    typ
  else
    (new lift_t k)#visit_typ 0 typ

class lift_p (k: int) = object
  inherit map_counting
  method! visit_PBound (i, _) j =
    if j < i then
      PBound j
    else
      PBound (j + k)
end

let lift_p (k: int) (pat: pattern): pattern =
  if k = 0 then
    pat
  else
    (new lift_p k)#visit_pattern_w 0 pat

(* ---------------------------------------------------------------------------- *)

(* Substitute [e2] for [i] in [e1]. *)

let subst_no_open (e2: expr) (i: int) (e1: expr) =
  (object
    inherit map_counting
    method! visit_EBound (i, _) j =
      if j = i then
        (lift i e2).node
      else
        EBound j
  end)#visit_expr_w i e1

(* ---------------------------------------------------------------------------- *)

(* Substitute [e2] for [i] in [e1]. These should be called [open]. *)

class subst (e2: expr) = object
  (* The environment [i] is the variable that we are looking for. *)
  inherit map_counting
  (* The target variable [i] is replaced with [t2]. Any other
     variable is unaffected. *)
  method! visit_EBound (i, _) j =
    if j = i then
      (lift i e2).node
    else
      EBound (if j < i then j else j-1)
end

let subst (e2: expr) (i: int) (e1: expr) =
  (new subst e2)#visit_expr_w i e1

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
  method! visit_TBound i j =
    if j = i then
      lift_t i t2
    else
      TBound (if j < i then j else j-1)
end

let subst_te (t2: typ) (i: int) (e1: expr) =
  (new subst_t t2)#visit_expr_w i e1

let subst_ten ts e =
  let l = List.length ts in
  KList.fold_lefti (fun i body arg ->
    let k = l - i - 1 in
    subst_te arg k body
  ) e ts

let subst_t (t2: typ) (i: int) (t1: typ) =
  (new subst_t t2)#visit_typ i t1

let subst_tn ts t =
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
  method! visit_PBound (i, _) j =
    if j = i then
      (lift_p i p2).node
    else
      PBound (if j < i then j else j-1)
end

let subst_p (p2: pattern) (i: int) (p1: pattern) =
  (new subst_p p2)#visit_pattern_w i p1

(* ---------------------------------------------------------------------------- *)

(* Close [binder] into bound variable i *)

class close (atom': Atom.t) (e: expr) = object
  inherit map_counting

  method! visit_EOpen (i, _) name atom =
    if Atom.equal atom atom' then
      (lift i e).node
    else
      EOpen (name, atom)
end

class close_p (atom': Atom.t) (p: pattern) = object
  inherit map_counting

  method! visit_POpen (i, _) name atom =
    if Atom.equal atom atom' then
      (lift_p i p).node
    else
      POpen (name, atom)
end

let close (a: Atom.t) (e': expr) (e: expr) =
  (new close a e')#visit_expr_w 0 e

let close_p (a: Atom.t) (e': pattern) (e: pattern) =
  (new close_p a e')#visit_pattern_w 0 e

let closing_binder b e =
  close b.node.atom (with_type b.typ (EBound 0)) (lift 1 e)

let close_binder_p b e =
  close_p b.node.atom (with_type b.typ (PBound 0)) (lift_p 1 e)

let close_binder = closing_binder

let close_binders bs e1 =
  List.fold_left (fun e1 b -> close_binder b e1) e1 bs

let close_binders_p bs e1 =
  List.fold_left (fun e1 b -> close_binder_p b e1) e1 bs

let close_branch bs p e =
  close_binders_p bs p, close_binders bs e

(* ---------------------------------------------------------------------------- *)

let opening_binder b =
  let a = Atom.fresh () in
  let b = { b with node = { b.node with atom = a } } in
  b, subst { node = EOpen (b.node.name, a); typ = b.typ } 0

let open_binder b e1 =
  let b, f = opening_binder b in
  b, f e1

let term_of_binder b =
  let a = b.node.atom in
  with_type b.typ (EOpen (b.node.name, a))

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

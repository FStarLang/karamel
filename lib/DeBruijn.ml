(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 and MIT Licenses. *)

(** This module provides various substitution functions. *)

(* ---------------------------------------------------------------------------- *)

open Ast
open PrintAst.Ops

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
  inherit map_counting as super

  (* The target variable [i] is replaced with [t2]. Any other
     variable is unaffected. We override visit_expr to be able to preserve meta
     information. *)
  method! visit_expr ((i, _) as env) e =
    match e.node with
    | EBound j ->
      if j = i then
        let e2 = lift i e2 in
        { e2 with meta = e2.meta @ e.meta }
      else
        { e with node = EBound (if j < i then j else j-1) }
    | _ ->
        super#visit_expr env e
end

let subst (e2: expr) (i: int) (e1: expr) =
  (new subst e2)#visit_expr_w i e1

let subst_n e es =
  let l = List.length es in
  KList.fold_lefti (fun i body arg ->
    let k = l - i - 1 in
    subst arg k body
  ) e es

let subst_n' ofs e es =
  let l = List.length es in
  KList.fold_lefti (fun i body arg ->
    let k = l - i - 1 in
    subst arg (k + ofs) body
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

let subst_tn' ofs ts t =
  let l = List.length ts in
  KList.fold_lefti (fun i body arg ->
    let k = l - i - 1 in
    subst_t arg (k + ofs) body
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
  b, subst { node = EOpen (b.node.name, a); typ = b.typ; meta = [] } 0

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
      subst_p { node = POpen (b.node.name, b.node.atom); typ = b.typ; meta = [] } 0 pat
    in
    b :: bs, pat, expr
  ) bs ([], pat, expr)

(* ---------------------------------------------------------------------------- *)

(* Const generic support *)

class map_counting_cg = object(self)
  (* The environment [i] has type [int*int]. *)
  inherit [_] map as _super
  (* The environment is a pair [i, i']. The first component [i] is the DeBruijn
    index we are looking for, after entering ONLY the cg binders. It it set by
    the caller and does not increase afterwards since the only cg binders are at
    the function declaration level. The second component [i'] is the DeBruijn
    index we are looking for, after entering ALL the binders. It is incremented
    at each binder, in expressions. *)
  method! extend ((i: int), i') (_: binder) =
    i, i' + 1

  method visit_TPoly (i, i') ts t =
    TPoly (ts, self#visit_typ (i + ts.n_cgs, i') t)

  method! visit_ETApp (((i, i'), env) as env0) e cgs cgs' ts =
    let n_cgs = match e.typ with
      | TPoly ({ n_cgs; _ }, _) -> n_cgs
      | _ -> List.length cgs
    in
    let env1 = (i + n_cgs, i'), env in
    ETApp (self#visit_expr env1 e,
      List.map (self#visit_expr env0) cgs,
      List.map (self#visit_expr env0) cgs',
      List.map (self#visit_typ (fst env0)) ts)
end

(* Converting an expression into a suitable const generic usable in types, knowing
   `diff = n_cg - n_binders`, where
   - n_cg is the total number of const generics in the current function / type,
     and
   - n_binders is the total number of expression binders traversed (including
     const generics) *)
let cg_of_expr diff e =
  match e.node with
  | EBound k ->
      assert (k - diff >= 0);
      CgVar (k - diff)
  | EConstant (w, s) ->
      CgConst (w, s)
  | _ ->
      failwith (KPrint.bsprintf "Unsuitable const generic: %a" pexpr e)

(* Substitute const generics *)
class subst_ct (c: cg Lazy.t) = object (self)
  (* There are no const generic binders -- nothing to increment *)
  inherit [_] map

  method visit_TPoly i ts t =
    TPoly (ts, self#visit_typ (i + ts.n_cgs) t)

  method! visit_TCgArray (i as env) t j =
    let t = self#visit_typ env t in
    (* We wish to replace i with c in [ t; j ] *)
    match Lazy.force c with
    | CgVar v' ->
        (* we substitute v' for i in [ t; j ] *)
        if j = i then
          TCgArray (t, v' + i (* = lift_cg i v' *))
        else
          TCgArray (t, if j < i then j else j-1)
    | CgConst (w, s) ->
        if j = i then
          TArray (t, (w, s))
        else
          TCgArray (t, if j < i then j else j-1)

  method! visit_TCgApp i t arg =
    let t = self#visit_typ i t in
    (* We are seeking to replace i with c in TCgApp (t, arg) *)
    match arg with
    | CgVar j ->
        (* We are visiting a TCgApp that contains a variable: that variable (the
           argument of the TCgApp) is a candidate for substitution. *)
        begin match Lazy.force c with
        | CgVar v' ->
            (* We substitute v' for i in TCgApp (t, CgVar j) *)
            if j = i then
              TCgApp (t, CgVar (v' + i) (* = lift_cg i v' *))
            else
              TCgApp (t, CgVar (if j < i then j else j-1))
        | CgConst _ as c ->
            (* We substitute c for i in TCgApp (t, CgVar j) *)
            if j = i then
              TCgApp (t, c)
            else
              TCgApp (t, CgVar (if j < i then j else j-1))
        end
    | _ ->
        TCgApp (t, arg)
end

(* Substitute const generics *)
class subst_c (diff: int) (c: expr) = object (_self)
  inherit map_counting_cg
  method! visit_typ ((i, _) as _env) t =
    let c = lazy (cg_of_expr diff c) in
    (new subst_ct c)#visit_typ i t

  method! visit_EBound ((_, i), _) j =
    if j = i then
      (lift i c).node
    else
      EBound (if j < i then j else j-1)
end

(* Both of these function receive a cg debruijn index, whereas the argument c is
 an expression that is in the expression debruijn space -- hence the extra diff
 parameter to go one the latter to the former. *)
let subst_ce diff c i = (new subst_c diff c)#visit_expr_w (i, i + diff)
let subst_ct diff c i = (new subst_c diff c)#visit_typ (i, i + diff)

let subst_cen diff cs t =
  let l = List.length cs in
  KList.fold_lefti (fun i body arg ->
    let k = l - i - 1 in
    let body = subst_ce diff arg k body in
    (* KPrint.bprintf "k=%d body=%a\n\n" k PrintAst.pexpr body; *)
    body
  ) t cs

let subst_ctn diff cs t =
  let l = List.length cs in
  KList.fold_lefti (fun i body arg ->
    let k = l - i - 1 in
    subst_ct diff arg k body
  ) t cs

let subst_ctn' cs t =
  let l = List.length cs in
  KList.fold_lefti (fun i body arg ->
    let k = l - i - 1 in
    (new subst_ct (lazy arg))#visit_typ k body
  ) t cs

let subst_ctn'' ofs cs t =
  let l = List.length cs in
  KList.fold_lefti (fun i body arg ->
    let k = l - i - 1 + ofs in
    (new subst_ct (lazy arg))#visit_typ k body
  ) t cs

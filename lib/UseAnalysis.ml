(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 and MIT Licenses. *)

open Ast
open DeBruijn
open Helpers

(* This module implements a tree traversal that updates the `mark` field of
   nodes (specifically: of let-binders, branch binders and function parameter
   binders) with information regarding the usage of those variables. This module
   computes two slightly different pieces of information.
   - The first one is whether a given variable occurs in the generated C *after*
     C preprocessing. This is called an occurrence, and computing it involves
     reasoning about ifdefs. This is used exclusively to defeat C compilers'
     unused variable warnings.
   - The second one is an upper bound on the number of uses of a given variable.
     We call it a usage, and it allows removing unused variables (i.e, used at
     most zero times), as well as inlining variables used at most once. Both of
     these optimizations are subject to various syntactic criteria.
*)

include Mark

(* Occurrences *)

(* Regular syntactic composition -- the nature of the AST node doesn't matter,
   it's all about whether the thing occurs for sure in the generated code or
   not. *)
let plus_regular o1 o2 =
  match o1, o2 with
  | MaybeAbsent, MaybeAbsent -> MaybeAbsent
  | _ -> Present

(* Composition under an ifdef -- after preprocessing, one of these will be gone. *)
let plus_ifdef o1 o2 =
  match o1, o2 with
  | Present, Present -> Present
  | _ -> MaybeAbsent

(* Usages *)

(* Sequential composition. Always correct, but sometimes conservative. *)
let plus_sequential u1 u2 =
  match u1, u2 with
  | AtMost n, AtMost m -> AtMost (n + m)

(* Disjunction in the control-flow. More precise than sequential composition. *)
let plus_disjunction u1 u2 =
  match u1, u2 with
  | AtMost n, AtMost m -> AtMost (max n m)

(* Valuations, i.e. the result of our analysis *)

type valuation = occurrence * usage

let zero: valuation = MaybeAbsent, AtMost 0

let plus (o1, u1) (o2, u2) =
  plus_regular o1 o2, plus_sequential u1 u2

let plus_if (o1, u1) (o2, u2) =
  plus_regular o1 o2, plus_disjunction u1 u2

let plus_ifdef (o1, u1) (o2, u2) =
  plus_ifdef o1 o2, plus_disjunction u1 u2

(* To avoid a mess with opening / closing each and every binder (quadratic), we
   rely on DeBruijn levels and clean the environment upon exiting a binder. *)

module IntMap = Map.Make(struct
  type t = int
  let compare = compare
end)

(* Restricts an intmap to levels < n *)
let restrict_map m n =
  IntMap.filter (fun k _ -> k < n) m

let plus_map (plus: valuation -> valuation -> valuation) (m1: valuation IntMap.t) (m2: valuation IntMap.t) =
  IntMap.merge (fun _ v1 v2 ->
    assert (not (v1 = None && v2 = None));
    let v1 = Stdlib.Option.value ~default:zero v1 in
    let v2 = Stdlib.Option.value ~default:zero v2 in
    Some (plus v1 v2)) m1 m2

(* This phase performs a usage and occurrence analysis and stores the result
   in the mark of binders which are in an ELet, a branch, or in a DFunction node
   (marks for all other binders, e.g. for-loop binders, are unspecified). *)
let build_usage_map_and_mark ifdefs = object(self)
  inherit [_] reduce as super

  method! extend env binder =
    binder :: env

  method zero: valuation IntMap.t = IntMap.empty
  method plus: valuation IntMap.t -> valuation IntMap.t -> valuation IntMap.t = plus_map plus

  method! visit_EBound (env, _) i =
    let level = List.length env - i - 1 in
    IntMap.singleton level (Present, AtMost 1)

  method! visit_EIfThenElse (env, _ as env_) e1 e2 e3 =
    (* This mimics the logic of mk_ifdef in AstToCStar *)
    let is_ifdef =
      match ifdefs with
      | None -> `No
      | Some ifdefs -> is_ifdef ifdefs e1
    in

    match is_ifdef with
    | `No ->
        (* We do not use plus_if here since the syntactic criteria
           (is_readonly_...) are not if-then-else aware so this would only lead
           us to perform more work for no good reason. *)
        super#visit_EIfThenElse env_ e1 e2 e3
    | `Yes ->
        let map = plus_map plus_ifdef (self#visit_expr_w env e2) (self#visit_expr_w env e3) in
        self#plus map (self#visit_expr_w env e1)
    | `YesWithExtra (e1, e2') ->
        (* e1 is the new condition of the if-then-else -- and e2' will also go
           underneath then then-branch with e2 *)
        let map_e2 = self#plus (self#visit_expr_w env e2) (self#visit_expr_w env e2') in
        let map = plus_map plus_ifdef map_e2 (self#visit_expr_w env e3) in
        self#plus map (self#visit_expr_w env e1)

  method! visit_ELet env b e1 e2 =
    let env0 = self#extend (fst env) b in
    let map = self#visit_expr_w env0 e2 in
    let level = List.length (fst env) in
    let v = match IntMap.find_opt level map with None -> zero | Some v -> v in
    b.node.mark := v;
    let map = restrict_map map level in
    if snd v = AtMost 0 && is_readonly_c_expression e1 then
      (* will be eliminated -- don't visit *)
      map
    else
      self#plus map (self#visit_expr env e1)

  method! visit_DFunction env cc flags n_cgs n ret name binders body =
    let map = super#visit_DFunction env cc flags n_cgs n ret name binders body in
    List.iteri (fun i b ->
      let v = match IntMap.find_opt i map with None -> zero | Some v -> v in
      b.node.mark := v
    ) binders;
    map

  method! visit_EFor env b e1 e2 e3 e4 =
    let env0 = self#extend (fst env) b in
    let map = KList.reduce self#plus [
      self#visit_expr_w env0 e2;
      self#visit_expr_w env0 e3;
      self#visit_expr_w env0 e4;
    ] in
    let level = List.length (fst env) in
    let v = match IntMap.find_opt level map with None -> zero | Some v -> v in
    b.node.mark := v;
    let map = restrict_map map level in
    (* May happen with interruptible_for... but we don't defeat the compiler
       warning in that case. TODO *)
    (* assert (snd v <> AtMost 0); *)
    self#plus map (self#visit_expr env e1)

  method! visit_branch env (binders, _, _ as b) =
    let map = super#visit_branch env b in
    let l = List.length (fst env) in
    List.iteri (fun i b ->
      let v = match IntMap.find_opt (l + i) map with None -> zero | Some v -> v in
      b.node.mark := v
    ) binders;
    restrict_map map l

  method! visit_EFun env bs e t =
    restrict_map (super#visit_EFun env bs e t) (List.length (fst env))
end

(* This phase uses the result of the usage and occurrence analysis above to i)
   eliminate unused variables, whenever possible; ii) insert KRML_HOST_IGNORE
   for variables that *may* end up being unused depending on the choice of
   ifdefs. This phase can be re-run multiple times -- it is stable, since
   inserting a KRML_HOST_IGNORE means the variable is now used and occurs,
   meaning a subsequent call to this will leave the variable untouched. *)
let use_mark_to_remove_or_ignore final = object (self)

  inherit [_] map as super

  method private remove_trivial_let e =
    match e with
    | ELet (_, e1, { node = EBound 0; _ }) when Helpers.is_readonly_c_expression e1 ->
        e1.node
    | _ ->
        e

  method! visit_ELet env b e1 e2 =
    (* Remove unused variables. Important to get rid of calls to [HST.get()]. *)
    let o, u = !(b.node.mark) in
    let is_readonly = is_readonly_c_expression e1 in
    let e1 = self#visit_expr env e1 in
    let e2 = self#visit_expr env e2 in
    if u = AtMost 0 then
      (* The variable is unused, for sure! Try to get rid of it using various
         mechanisms. The last one may result in spurious ignores over values,
         but that's ok. *)
      if is_readonly then
        self#remove_trivial_let (snd (open_binder b e2)).node
      else if e1.typ = TUnit then
        self#remove_trivial_let (ELet ({ b with node = { b.node with meta = Some MetaSequence }}, e1, e2))
      (* Definitely unused, except we can't generate let _ = ignore (bufcreate
         ...) -- this is a bad idea, as it'll force the hoisting phase to hoist
         the bufcreate back into a let-binding, which will then be named "buf". *)
      else if not (is_bufcreate e1) && Helpers.is_value e1 then
        ELet ({ node = { b.node with meta = Some MetaSequence }; typ = TUnit; meta = []},
          push_ignore e1,
          e2)
      (* Definitely unused, push an ignore at depth *)
      else
        ELet (b, e1, with_type e2.typ (
          ELet (sequence_binding (),
            push_ignore (with_type b.typ (EBound 0)),
            DeBruijn.lift 1 e2)))
    else if o = MaybeAbsent then
      (* The variable may be unused! So we can't mess the
         computation and push an ignore within e1. All we can do is wrap a
         reference to the variable in KRML_HOST_IGNORE to prevent compiler
         warnings. *)
      ELet (b, e1, with_type e2.typ (
        ELet (sequence_binding (),
          push_ignore (with_type b.typ (EBound 0)),
          DeBruijn.lift 1 e2)))
    else
      (* Nothing to do *)
      self#remove_trivial_let (ELet (b, e1, e2))

  method! visit_DFunction env cc flags n_cgs n ret name binders body =
    if not final then
      (* This is not the final phase, so we're still waiting for the removal of
         unused function parameters in private (non-externally visible)
         functions. This is done in a dedicated phase called `remove_unused`
         that relies on `unused_parameter_table`. *)
      super#visit_DFunction env cc flags n_cgs n ret name binders body
    else
      let env = List.fold_left self#extend env binders in
      let body = self#visit_expr_w env body in
      let l = List.length binders in
      let ignores = List.mapi (fun i b ->
        let o, _ = !(b.node.mark) in
        if o = MaybeAbsent && b.typ <> TUnit then
          (* unit arguments will be eliminated, always, based on a type analysis *)
          Some (push_ignore (with_type b.typ (EBound (l - i - 1))))
        else
          None
      ) binders in
      let ignores = KList.filter_some ignores in
      let body =
        if ignores = [] then
          body
        else
          List.fold_right (fun i body ->
            let b = sequence_binding () in
            with_type body.typ (ELet (b, i, DeBruijn.lift 1 body))
          ) ignores body
      in
      DFunction (cc, flags, n_cgs, n, ret, name, binders, body)


end


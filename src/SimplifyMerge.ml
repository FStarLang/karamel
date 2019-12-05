(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 License. *)

(** Merging variables together to avoid un-necessary let-bindings *)

open Ast
open DeBruijn
open PrintAst

module S = Set.Make(Atom)
module M = Map.Make(Atom)

let keys (type a) (m: a M.t): S.t =
  M.fold (fun k _ acc -> S.add k acc) m S.empty

let p env (x: S.t) =
  let l = List.map (fun x -> snd (M.find x env)) (S.elements x) in
  String.concat ", " l

(* Only meaningful when all binders are open *)
let replace_atom (a: Atom.t) (a': Atom.t) (e: expr) =
  (object
    inherit [_] map
    method! visit_EOpen _ i' a'' =
      let a = if a = a'' then a' else a'' in
      EOpen (i', a)

  end)#visit_expr_w () e

(* This function receives:
 * - env, the map of all the variables in scope to their types
 * - the set U of variables from env that are no longer dead because they
 *   were used and assigned to at some point
 * - an expression e to rewrite
 * it returns:
 * - a rewritten term e'
 * - the set D of variables from env that were dead in e pre-rewriting
 * - an updated set U'.
 * Therefore, the set of dead variables in e' (rewritten) is D - U'.
 * Therefore, the set of candidates for reusing a variable slot is env - U'. *)
let rec merge (env: (typ * ident) M.t) (u: S.t) (e: expr): S.t * S.t * expr =
  let w = with_type e.typ in
  match e.node with
  | ETApp _
  | ETuple _
  | EMatch _
  | ECons _
  | ESequence _
  | EFun _
  | EBound _ ->
      failwith "impossible (simplified before)"

  | EQualified _
  | EConstant _
  | EUnit
  | EBool _
  | EString _
  | EAny
  | EOp _
  | EPushFrame
  | EPopFrame
  | EEnum _
  | EAbort _ ->
      keys env, u, e

  | EOpen (_, a) ->
      S.remove a (keys env), u, e

  | ECast (e, t) ->
      let d, u, e = merge env u e in
      d, u, w (ECast (e, t))

  | EIgnore e ->
      let d, u, e = merge env u e in
      d, u, w (EIgnore e)

  | EApp (e, es) ->
      let d, u, e = merge env u e in
      let d, u, es = List.fold_left (fun (d, u, es) e ->
        let d', u, e = merge env u e in
        S.inter d d', u, e :: es
      ) (d, u, []) es in
      d, u, w (EApp (e, List.rev es))

  | ELet (b, e1, e2) ->
      (* Following the reverse order of control-flow for u *)
      let b, e2 = open_binder b e2 in
      let env = M.add b.node.atom (b.typ, b.node.name) env in
      let d2, u, e2 = merge env u e2 in

      (* For later *)
      let d1, u_final, e1 = merge env u e1 in
      let d_final = S.inter d1 d2 in

      (* TODO: find_valid predicate *)
      begin match M.fold (fun x (t, i) acc ->
        match acc with
        | None when
          t = b.typ && not (S.mem x u) && not (Atom.equal x b.node.atom) && S.mem x d1 ->
            Some (x, i)
        | _ ->
            acc
      ) env None with
      | Some (y, i) ->
          (* We are now rewriting:
           *   let x: t = e1 in e2
           * into:
           *   let _ = y := e1 in // will be made a sequence later
           *   e2 *)
          let e2 = replace_atom b.node.atom y e2 in
          KPrint.bprintf "In the let-binding for %s:\n\
            Dead in e2: %s\n\
            Used in e2: %s\n\
            Chose: %s\n\
            e2 now: %a\n\n" b.node.name (p env d2) (p env u) i pexpr e2;
          let e = ELet (Helpers.sequence_binding (),
            with_type TUnit (EAssign (
              with_type b.typ (EOpen (i, y)),
              e1)),
            e2)
          in
          d_final, S.add y u_final, w e
      | None ->
          let mut = if S.mem b.node.atom u_final then true else false in
          let b = { b with node = { b.node with mut }} in
          let e = ELet (b, e1, close_binder b e2) in
          d_final, u_final, w e
      end


  | EIfThenElse _ -> Warn.fatal_error "TODO: EIfThenElse"
  | EAssign _ -> Warn.fatal_error "TODO: EAssign"
  | EBufCreate _ -> Warn.fatal_error "TODO: EBufCreate"
  | EBufCreateL _ -> Warn.fatal_error "TODO: EBufCreateL"
  | EBufRead _ -> Warn.fatal_error "TODO: EBufRead"
  | EBufWrite _ -> Warn.fatal_error "TODO: EBufWrite"
  | EBufSub _ -> Warn.fatal_error "TODO: EBufSub"
  | EBufBlit _ -> Warn.fatal_error "TODO: EBufBlit"
  | EBufFill _ -> Warn.fatal_error "TODO: EBufFill"
  | EBufFree _ -> Warn.fatal_error "TODO: EBufFree"
  | ESwitch _ -> Warn.fatal_error "TODO: ESwitch"
  | EFlat _ -> Warn.fatal_error "TODO: EFlat"
  | EField _ -> Warn.fatal_error "TODO: EField"
  | EBreak -> Warn.fatal_error "TODO: EBreak"
  | EReturn _ -> Warn.fatal_error "TODO: EReturn"
  | EWhile _ -> Warn.fatal_error "TODO: EWhile"
  | EFor _ -> Warn.fatal_error "TODO: EFor"
  | EComment _ -> Warn.fatal_error "TODO: EComment"
  | EAddrOf _ -> Warn.fatal_error "TODO: EAddrOf"

let merge_visitor = object(_)
  inherit [_] map
  method! visit_DFunction () cc flags n ret name binders body =
    let binders, body = open_binders binders body in
    let _, _, body = merge M.empty S.empty body in
    let body = close_binders binders body in
    DFunction (cc, flags, n, ret, name, binders, body)
end

(* Debug any intermediary AST as follows: *)
(* PPrint.(Print.(print (PrintAst.print_files files ^^ hardline))); *)

let simplify files =
  let files = Simplify.sequence_to_let#visit_files () files in
  let files = merge_visitor#visit_files () files in
  PPrint.(Print.(print (PrintAst.print_files files ^^ hardline)));
  let files = Simplify.let_to_sequence#visit_files () files in
  files

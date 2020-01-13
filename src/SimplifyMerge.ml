(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 License. *)

(** Merging variables together to avoid un-necessary let-bindings *)

open Ast
open DeBruijn
open PrintAst

module S = Set.Make(Atom)
module M = Map.Make(Atom)

let debug = false

type env = (Atom.t * (typ * bool * ident)) list

let keys (e: env): S.t =
  List.fold_left (fun acc (k, _) -> S.add k acc) S.empty e

let extend x y (env: env) =
  (x, y) :: env

let find =
  List.assoc

(* Print elements of x based on atom -> ident mapping in env *)
let p (env: env) (x: S.t) =
  let l = List.map (fun x ->
    try let _, _, i = find x env in i with Not_found -> "?"
  ) (S.elements x) in
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
 * - env, an associative list of all the variables in scope to their types
 * - the set U of variables from env that are no longer dead because they
 *   were used and assigned to at some point
 * - an expression e to rewrite
 * it returns:
 * - a rewritten term e'
 * - the set D of variables from env that were dead in e pre-rewriting
 * - an updated set U'.
 * Therefore, the set of dead variables in e' (rewritten) is D - U'.
 * Therefore, the set of candidates for reusing a variable slot is env - U'. *)
let rec merge' (env: env) (u: S.t) (e: expr): S.t * S.t * expr =
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
  | EStandaloneComment _
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
      let d, u, es = merge_list env d u es in
      d, u, w (EApp (e, es))

  | ELet (b, e1, e2) ->
      (* Following the reverse order of control-flow for u *)
      let b, e2 = open_binder b e2 in
      let has_storage t e1 =
        match t, e1.node with
        | TArray _, _
        | _, EBufCreate (Stack, _, _)
        | _, EBufCreateL (Stack, _) ->
            true
        | _ ->
            false
      in
      let env' = extend b.node.atom (b.typ, has_storage b.typ e1, b.node.name) env in
      let d2, u, e2 = merge env' u e2 in

      let candidate =
        match e1.node with
        | EBufCreateL _ | EBufCreate (_, _, _) ->
            (* I guess we could allow heap-allocated buffers to reuse variables,
             * but CStarToC11 doesn't allow it (why?). *)
            None
        | _ ->
            let rec common_prefix i s1 s2 =
              if String.length s1 = i || String.length s2 = i then
                i
              else if s1.[i] = s2.[i] then
                common_prefix (i + 1) s1 s2
              else
                i
            in

            let fits x t has_storage i =
              (* Compatible type *)
              t = b.typ &&
              (* Hasn't been used further down the control-flow *)
              not (S.mem x u) &&
              (* No self-assignments *)
              not (Atom.equal x b.node.atom) &&
              (* Must be dead *)
              S.mem x d2 &&
              (* Ignore sequence let-bindings *)
              not (t = TUnit) &&
              (* Array types are not assignable *)
              not has_storage &&
              (* If in prefix mode, must find a common prefix *)
              (Options.(!merge_variables <> Prefix) || common_prefix 0 i b.node.name > 0)
            in
            KList.find_opt (fun (x, (t, h, i)) -> if fits x t h i then Some (x, i) else None) env
      in

      (* For later *)
      let d1, u_final, e1 = merge env u e1 in
      let d_final = S.inter d1 d2 in

      (* Note: thanks to the fact we encode the environment as a list, we can
       * apply a heuristic, which is to use the nearest binding. *)
      begin match candidate with
      | Some (y, i) ->
          (* We are now rewriting:
           *   let x: t = e1 in e2
           * into:
           *   let _ = y := e1 in // will be made a sequence later
           *   e2 *)
          let e2 = replace_atom b.node.atom y e2 in
          if debug then
            KPrint.bprintf "In the let-binding for %s:\n\
              Dead in e2: %s\n\
              Used in e2: %s\n\
              Chose: %s\n\
              e2 now: %a\n\n" b.node.name (p env d2) (p env u) i pexpr e2;
          let self_assignment =
            match e1.node with
            | EOpen (_, x1) when Atom.equal x1 y ->
                true
            | _ ->
                false
          in
          let e =
            if e1.node = EAny then
              e2.node
            else if self_assignment then
              e2.node
            else
              ELet (Helpers.sequence_binding (),
                with_type TUnit (EAssign (
                  with_type b.typ (EOpen (i, y)),
                  e1)),
                e2)
          in
          d_final, S.add y u_final, w e
      | None ->
          if debug then
            KPrint.bprintf "In the let-binding for %s:\n\
              Dead in e2: %s\n\
              Used in e2: %s\n\
              No candidate\n\n" b.node.name (p env d2) (p env u);

          let mut = if S.mem b.node.atom u_final then true else b.node.mut in
          let b = { b with node = { b.node with mut }} in
          let e = ELet (b, e1, close_binder b e2) in
          d_final, u_final, w e
      end


  | EIfThenElse (e1, e2, e3) ->
      let d2, u2, e2 = merge env u e2 in
      let d3, u3, e3 = merge env u e3 in
      let d1, u, e1 = merge env (S.union u2 u3) e1 in
      S.inter (S.inter d1 d2) d3, u, w (EIfThenElse (e1, e2, e3))

  | EAssign (e1, e2) ->
      let d2, u, e2 = merge env u e2 in
      let d1, u, e1 = merge env u e1 in
      S.inter d1 d2, u, w (EAssign (e1, e2))

  | EBufRead (e1, e2) ->
      let d2, u, e2 = merge env u e2 in
      let d1, u, e1 = merge env u e1 in
      S.inter d1 d2, u, w (EBufRead (e1, e2))

  | EBufCreate (l, e1, e2) ->
      let d2, u, e2 = merge env u e2 in
      let d1, u, e1 = merge env u e1 in
      S.inter d1 d2, u, w (EBufCreate (l, e1, e2))

  | EBufCreateL (l, es) ->
      let d, u, es = merge_list env (keys env) u es in
      d, u, w (EBufCreateL (l, es))

  | EBufWrite (e1, e2, e3) ->
      let d1, u, e1 = merge env u e1 in
      let d2, u, e2 = merge env u e2 in
      let d3, u, e3 = merge env u e3 in
      S.inter (S.inter d1 d2) d3, u, w (EBufWrite (e1, e2, e3))

  | EBufSub (e1, e2) ->
      let d1, u, e1 = merge env u e1 in
      let d2, u, e2 = merge env u e2 in
      S.inter d1 d2, u, w (EBufSub (e1, e2))

  | EBufBlit (e1, e2, e3, e4, e5) ->
      let d1, u, e1 = merge env u e1 in
      let d2, u, e2 = merge env u e2 in
      let d3, u, e3 = merge env u e3 in
      let d4, u, e4 = merge env u e4 in
      let d5, u, e5 = merge env u e5 in
      KList.reduce S.inter [ d1; d2; d3; d4; d5 ], u, w (EBufBlit (e1, e2, e3, e4, e5))

  | EBufFill (e1, e2, e3) ->
      let d1, u, e1 = merge env u e1 in
      let d2, u, e2 = merge env u e2 in
      let d3, u, e3 = merge env u e3 in
      S.inter (S.inter d1 d2) d3, u, w (EBufFill (e1, e2, e3))

  | EBufFree e1 ->
      let d1, u, e1 = merge env u e1 in
      d1, u, w (EBufFree e1)

  | ESwitch (e, es) ->
      let ds, us, es = List.fold_left (fun (ds, us, es) (c, e) ->
        let d, u, e = merge env u e in
        d :: ds, u :: us, (c, e) :: es
      ) ([], [], []) es in
      let es = List.rev es in
      let u = KList.reduce S.union us in
      let d, u, e = merge env u e in
      let d = KList.reduce S.inter (d :: ds) in
      d, u, w (ESwitch (e, es))

  | EFlat fieldexprs ->
      let fs, es = List.split fieldexprs in
      let d, u, es = merge_list env (keys env) u es in
      let fieldexprs = List.combine fs es in
      d, u, w (EFlat fieldexprs)

  | EField (e, f) ->
      let d, u, e = merge env u e in
      d, u, w (EField (e, f))

  | EWhile (e1, e2) ->
      let d2, u, e2 = merge env u e2 in
      let d1, u, e1 = merge env u e1 in
      S.inter d1 d2, u, w (EWhile (e1, e2))

  | EBreak ->
      keys env, u, w EBreak

  | EReturn e ->
      let d, u, e = merge env u e in
      d, u, w (EReturn e)

  | EFor (b, e1, e2, e3, e4) ->
      let binder, s = opening_binder b in
      let e2 = s e2 and e3 = s e3 and e4 = s e4 in
      let d4, u, e4 = merge env u e4 in
      let d3, u, e3 = merge env u e3 in
      let d2, u, e2 = merge env u e2 in
      let d1, u, e1 = merge env u e1 in
      let s = closing_binder binder in
      KList.reduce S.inter [ d1; d2; d3; d4 ], u, w (EFor (b, e1, s e2, s e3, s e4))

  | EComment (s1, e, s2) ->
      let d, u, e = merge env u e in
      d, u, w (EComment (s1, e, s2))

  | EAddrOf e ->
      let d, u, e = merge env u e in
      d, u, w (EAddrOf e)

and merge (env: env) (u: S.t) (e: expr): S.t * S.t * expr =
  let d, u, e = merge' env u e in
  if debug then
    KPrint.bprintf "After visiting %a: D=%s\n" pexpr e (p env d);
  d, u, e

and merge_list env d u es =
  let d, u, es =
    List.fold_left (fun (d, u, es) e ->
      let d', u, e = merge env u e in
      S.inter d d', u, e :: es
    ) (d, u, []) es
  in
  d, u, List.rev es

let merge_visitor = object(_)
  inherit [_] map
  method! visit_DFunction () cc flags n ret name binders body =
    if debug then
      KPrint.bprintf "Variable merge: visiting %a\n%a\n" plid name ppexpr body;
    let binders, body = open_binders binders body in
    let _, _, body = merge [] S.empty body in
    let body = close_binders binders body in
    DFunction (cc, flags, n, ret, name, binders, body)
end

(* Debug any intermediary AST as follows: *)
(* PPrint.(Print.(print (PrintAst.print_files files ^^ hardline))); *)

let simplify files =
  let files = Simplify.sequence_to_let#visit_files () files in
  let files = merge_visitor#visit_files () files in
  if debug then
    PPrint.(Print.(print (PrintAst.print_files files ^^ hardline)));
  let files = Simplify.let_to_sequence#visit_files () files in
  files

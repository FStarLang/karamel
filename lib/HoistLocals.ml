(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 and MIT Licenses. *)

(* Hoist all local variable declarations to the beginning of the function body,
   in the order they appear, preserving comments in between.

   Controlled by -fhoist-locals.

   Algorithm: we walk the body of each function, collecting ELet declarations.

   For a given local variable declaration, after hoisting any locals from its
   initializer expression:
   - If no statements other than variable declarations and comments were
     produced (i.e. we are still in the "declaration zone" at the top of the
     body), keep the declaration with its initializer.
   - Otherwise, emit the declaration without its initializer (using EAny) at
     the end of the already-produced declarations, and turn the initializer
     into an assignment at the original location.

   Special case: if a locally allocated array has a non-constant size (VLA)
   and needs to be lifted past real statements, emit a warning (fatal by
   default), leave the declaration in place, and continue. *)

open Ast
open Helpers
open DeBruijn

(* Does an EBufCreate have a non-constant size (VLA)? *)
let is_vla e1 =
  match e1.node with
  | EBufCreate (Common.Stack, _, size) ->
      (match size.node with EConstant _ -> false | _ -> true)
  | _ -> false

(* An opened binder + its initializer (or EAny if split). *)
type hoisted = {
  b: binder;
  init: expr;
}

(* Prepend a statement before a body, flattening into ESequence. *)
let prepend stmt body typ =
  match body.node with
  | ESequence es -> { node = ESequence (stmt :: es); typ; meta = [] }
  | _ -> { node = ESequence [stmt; body]; typ; meta = [] }

(* Walk a body expression, collecting declarations to hoist.

   [only_decls]: true when all preceding statements at this function level have
   been declarations or comments, so the next declaration can keep its init.

   Returns (hoisted_decls, residual_body).
   hoisted_decls are in source order with opened binders.
   residual_body uses EOpen references to those binders. *)
let rec hoist ~only_decls (e: expr) : hoisted list * expr =
  match e.node with

  (* Real local variable declaration. *)
  | ELet (b, e1, e2) when not (List.mem MetaSequence b.node.meta) ->
      (* First, hoist any locals from the initializer. *)
      let init_h, e1_r = hoist ~only_decls:true e1 in
      let init_has_stmts = residual_has_stmts e1_r in

      (* Open the binder for the continuation. *)
      let b_o, e2_o = open_binder b e2 in

      if only_decls && not init_has_stmts then begin
        (* Still in the declaration zone. Keep the initializer. *)
        let rest_h, rest_body = hoist ~only_decls:true e2_o in
        (init_h @ [{ b = b_o; init = e1_r }] @ rest_h, rest_body)
      end else if is_vla e1 && not only_decls then begin
        (* VLA that would need to cross real statements: warn, leave in place. *)
        Warn.(maybe_fatal_error ("", Error.HoistLocalsVla b_o.node.name));
        let rest_h, rest_body = hoist ~only_decls:false e2_o in
        let residual =
          { node = ELet (b_o, e1_r, close_binder b_o rest_body);
            typ = e.typ; meta = e.meta } in
        (init_h @ rest_h, residual)
      end else if is_bufcreate e1 then begin
        (* Buffer creation must remain under its let-binding (required by
           later passes). Leave the declaration in place. *)
        let rest_h, rest_body = hoist ~only_decls:false e2_o in
        let residual =
          { node = ELet (b_o, e1_r, close_binder b_o rest_body);
            typ = e.typ; meta = e.meta } in
        (init_h @ rest_h, residual)
      end else begin
        (* Past the declaration zone: separate declaration from initializer. *)
        let b_mut = mark_mut b_o in
        let decl = { b = b_mut;
                     init = { node = EAny; typ = b_o.typ; meta = [] } } in
        let rest_h, rest_body = hoist ~only_decls:false e2_o in
        (* If the init is already EAny, no assignment is needed. *)
        if e1_r.node = EAny then
          (init_h @ [decl] @ rest_h, rest_body)
        else
          let assign =
            { node = EAssign (
                { node = EOpen (b_o.node.name, b_o.node.atom);
                  typ = b_o.typ; meta = [] },
                e1_r);
              typ = TUnit; meta = [] } in
          (init_h @ [decl] @ rest_h, prepend assign rest_body e.typ)
      end

  (* Push/pop frame markers: these are structural, not real statements.
     Hoist INSIDE the push frame: we collect declarations from e2 and
     place them at the start of e2 (inside the ELet). *)
  | ELet (_, { node = EPushFrame; _ }, e2) ->
      let inner_h, inner_body = hoist ~only_decls:true e2 in
      let inner_body = rebuild inner_h inner_body in
      let b_seq = sequence_binding () in
      ([], { node = ELet (b_seq,
               { node = EPushFrame; typ = TUnit; meta = [] },
               close_binder b_seq inner_body);
             typ = e.typ; meta = e.meta })

  (* EPopFrame at the end of a body. *)
  | EPopFrame ->
      ([], e)

  (* MetaSequence binding: a sequencing construct, not a variable declaration.
     This marks the transition from decl zone to statement zone. *)
  | ELet (b, e1, e2) ->
      let _, e2_o = open_binder b e2 in
      let rest_h, rest_body = hoist ~only_decls:false e2_o in
      (rest_h, prepend e1 rest_body e.typ)

  (* Statement sequence. *)
  | ESequence es ->
      hoist_seq ~only_decls e.typ e.meta es

  (* Comments don't affect only_decls status. *)
  | EStandaloneComment _ ->
      ([], e)

  (* Any other expression is a "real statement" — nothing to hoist from it. *)
  | _ ->
      ([], e)

(* Process a list of sequenced expressions. *)
and hoist_seq ~only_decls typ meta = function
  | [] -> ([], { node = ESequence []; typ; meta })
  | [e] -> hoist ~only_decls e
  | e :: rest ->
      let e_h, e_r = hoist ~only_decls e in
      let next_only = only_decls && is_decl_or_comment e in
      let rest_h, rest_r = hoist_seq ~only_decls:next_only typ meta rest in
      let combined = flatten_seq e_r rest_r typ meta in
      (e_h @ rest_h, combined)

(* Is this node a comment, a real variable declaration, or a push/pop frame? *)
and is_decl_or_comment e =
  match e.node with
  | EStandaloneComment _ -> true
  | EPushFrame -> true
  | EPopFrame -> true
  | ELet (b, _, _) when not (List.mem MetaSequence b.node.meta) -> true
  | _ -> false

(* Check whether an expression has had statements injected. *)
and residual_has_stmts e =
  match e.node with
  | EAssign _ -> true
  | ESequence es -> List.exists residual_has_stmts es
  | ELet (b, _, _) when List.mem MetaSequence b.node.meta -> true
  | _ -> false

(* Combine two residual expressions into a flat sequence. *)
and flatten_seq e1 e2 typ meta =
  let es1 = match e1.node with ESequence es -> es | _ -> [e1] in
  let es2 = match e2.node with ESequence es -> es | _ -> [e2] in
  match es1 @ es2 with
  | [e] -> e
  | es -> { node = ESequence es; typ; meta }

(* Rebuild: place hoisted declarations at the top, then the residual body. *)
and rebuild hoisted body =
  List.fold_right (fun { b; init } acc ->
    { node = ELet (b, init, close_binder b acc);
      typ = acc.typ; meta = [] }
  ) hoisted body

(* Entry point: transform all function declarations. *)
let hoist_locals (files: files) : files =
  (object
    inherit [_] map

    method! visit_DFunction _ cc flags n_cg n ret name binders body =
      let hoisted, body' = hoist ~only_decls:true body in
      let body' = rebuild hoisted body' in
      DFunction (cc, flags, n_cg, n, ret, name, binders, body')
  end)#visit_files () files

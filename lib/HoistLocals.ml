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

(* A hoisted item: either a local variable declaration (opened binder + its
   initializer, or EAny if split) or a standalone comment. *)
type hoisted =
  | HDecl of binder * expr
  | HComment of string

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
        (init_h @ [HDecl (b_o, e1_r)] @ rest_h, rest_body)
      end else if is_vla e1 then begin
        (* VLA: emit warning, leave the declaration in place. *)
        Warn.(maybe_fatal_error ("", Error.HoistLocalsVla b_o.node.name));
        let rest_h, rest_body = hoist ~only_decls:false e2_o in
        let residual =
          { node = ELet (b_o, e1_r, close_binder b_o rest_body);
            typ = e.typ; meta = e.meta } in
        (init_h @ rest_h, residual)
      end else begin
        match e1_r.node with
        | EBufCreate (l, init, size) ->
            (* Constant-size buffer: hoist the declaration with EAny init,
               emit EBufFill at original location. *)
            let decl_init =
              { e1_r with node = EBufCreate (l,
                  { node = EAny; typ = init.typ; meta = [] }, size) } in
            let buf_ref =
              { node = EOpen (b_o.node.name, b_o.node.atom);
                typ = b_o.typ; meta = [] } in
            let fill =
              { node = EBufFill (buf_ref, init, size);
                typ = TUnit; meta = [] } in
            let rest_h, rest_body = hoist ~only_decls:false e2_o in
            (init_h @ [HDecl (b_o, decl_init)] @ rest_h,
             prepend fill rest_body e.typ)
        | EBufCreateL (l, inits) ->
            (* Buffer from literal list: hoist the declaration with EAny
               elements, emit individual EBufWrite for each element at
               original location. *)
            let any_init = { node = EAny; typ = (List.hd inits).typ; meta = [] } in
            let decl_init =
              { e1_r with node = EBufCreateL (l,
                  List.map (fun _ -> any_init) inits) } in
            let buf_ref =
              { node = EOpen (b_o.node.name, b_o.node.atom);
                typ = b_o.typ; meta = [] } in
            let writes = List.mapi (fun i ei ->
                let idx = { node = EConstant (K.UInt32, string_of_int i);
                            typ = TInt K.UInt32; meta = [] } in
                { node = EBufWrite (buf_ref, idx, ei);
                  typ = TUnit; meta = [] }
            ) inits in
            let rest_h, rest_body = hoist ~only_decls:false e2_o in
            let body' = List.fold_right
              (fun w acc -> prepend w acc e.typ) writes rest_body in
            (init_h @ [HDecl (b_o, decl_init)] @ rest_h, body')
        | _ ->
            (* Non-buffer: separate declaration from initializer. *)
            let b_mut = mark_mut b_o in
            let decl = HDecl (b_mut,
                         { node = EAny; typ = b_o.typ; meta = [] }) in
            let rest_h, rest_body = hoist ~only_decls:false e2_o in
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

  (* MetaSequence binding whose expression is a standalone comment: in the
     declaration zone, hoist the comment and keep collecting declarations. *)
  | ELet (b, { node = EStandaloneComment s; _ }, e2) when only_decls ->
      let _, e2_o = open_binder b e2 in
      let rest_h, rest_body = hoist ~only_decls:true e2_o in
      (HComment s :: rest_h, rest_body)

  (* MetaSequence binding: a sequencing construct, not a variable declaration.
     This marks the transition from decl zone to statement zone. *)
  | ELet (b, e1, e2) ->
      let _, e2_o = open_binder b e2 in
      let rest_h, rest_body = hoist ~only_decls:false e2_o in
      (rest_h, prepend e1 rest_body e.typ)

  (* Statement sequence. *)
  | ESequence es ->
      hoist_seq ~only_decls e.typ e.meta es

  (* In the declaration zone, hoist comments along with declarations so
     they maintain their position relative to initialised declarations. *)
  | EStandaloneComment s when only_decls ->
      ([HComment s], { node = ESequence []; typ = e.typ; meta = [] })

  (* Outside the declaration zone, leave comments in place. *)
  | EStandaloneComment _ ->
      ([], e)

  (* Branching constructs: recurse into their sub-bodies to hoist any
     local declarations up to the function level. *)
  | EIfThenElse (e1, e2, e3) ->
      let h2, e2' = hoist ~only_decls:false e2 in
      let h3, e3' = hoist ~only_decls:false e3 in
      (h2 @ h3, { e with node = EIfThenElse (e1, e2', e3') })

  | ESwitch (e1, branches) ->
      let hs, branches' = List.split (List.map (fun (c, body) ->
        let h, body' = hoist ~only_decls:false body in
        (h, (c, body'))
      ) branches) in
      (List.flatten hs, { e with node = ESwitch (e1, branches') })

  | EWhile (e1, e2) ->
      let h2, e2' = hoist ~only_decls:false e2 in
      (h2, { e with node = EWhile (e1, e2') })

  | EFor (b, e1, e2, e3, e4) ->
      let h4, e4' = hoist ~only_decls:false e4 in
      (h4, { e with node = EFor (b, e1, e2, e3, e4') })

  | EMatch (flav, e1, branches) ->
      let hs, branches' = List.split (List.map (fun (bs, pat, body) ->
        let h, body' = hoist ~only_decls:false body in
        (h, (bs, pat, body'))
      ) branches) in
      (List.flatten hs, { e with node = EMatch (flav, e1, branches') })

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

(* Rebuild: place hoisted declarations and comments at the top, then the
   residual body.  Comments are emitted as EStandaloneComment nodes inside
   ESequence wrappers so that AstToCStar processes them as proper statement-
   level comments, preserving their individual identity and source order. *)
and rebuild hoisted body =
  List.fold_right (fun h acc ->
    match h with
    | HDecl (b, init) ->
        { node = ELet (b, init, close_binder b acc);
          typ = acc.typ; meta = [] }
    | HComment s ->
        let c = { node = EStandaloneComment s; typ = TUnit; meta = [] } in
        match acc.node with
        | ESequence es -> { acc with node = ESequence (c :: es) }
        | _ -> { node = ESequence [c; acc]; typ = acc.typ; meta = [] }
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

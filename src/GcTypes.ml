(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 License. *)

(* Transformations specifically in support of types marked as GcType. We
 * essentially heap-allocate every constructor, then make sure that destructors
 * (pattern-matches, field accessors) dereference their argument. *)

open Ast
open Helpers

module C = Common

let mk_table files =
  Helpers.build_map files (fun map -> function
    | DType (lid, flags, _, _) when List.mem C.GcType flags ->
        Hashtbl.add map lid ()
    | _ ->
        ()
  )

let just_gc'd table = function
  | TBuf (TApp (lid, _), _)
  | TBuf (TQualified lid, _) when Hashtbl.mem table lid ->
      true
  | _ ->
      false

let alloc table = object (self)

  inherit [_] map

  method! visit_TQualified _env lid =
    (* Every occurrence of t becomes TBuf t *)
    if Hashtbl.mem table lid then
      TBuf (TQualified lid, false) (* JP: should attempt const here? *)
    else
      TQualified lid

  method! visit_TApp env lid ts =
    let ts = List.map (self#visit_typ env) ts in
    if Hashtbl.mem table lid then
      TBuf (TApp (lid, ts), false)
    else
      TApp (lid, ts)

  method! visit_PCons (env, t) cons args =
    (* A cons pattern needs to dereference the scrutinee first. *)
    let args = List.map (self#visit_pattern_w env) args in
    if just_gc'd table t then
      PDeref (with_type (assert_tbuf t) (PCons (cons, args)))
    else
      PCons (cons, args)

  method! visit_PRecord (env, t) fields =
    (* Same for record patterns *)
    let fields = List.map (fun (f, t) -> f, self#visit_pattern_w env t) fields in
    if just_gc'd table t then
      PDeref (with_type (assert_tbuf t) (PRecord fields))
    else
      PRecord fields

  method! visit_ECons (env, t) cons args =
    (* Constructors now heap-allocate. *)
    let args = List.map (self#visit_expr_w env) args in
    if just_gc'd table t then
      EBufCreate (C.Eternal, with_type (assert_tbuf t) (ECons (cons, args)), Helpers.oneu32)
    else
      ECons (cons, args)

  method! visit_EField env e f =
    (* A field destructor must dereference. *)
    let e = self#visit_expr env e in
    if just_gc'd table e.typ then
      EField (with_type (assert_tbuf e.typ) (EBufRead (e, Helpers.zerou32)), f)
    else
      EField (e, f)

end

let heap_allocate_gc_types files =
  let table = mk_table files in
  let files = (alloc table)#visit_files () files in
  files

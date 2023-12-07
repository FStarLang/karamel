(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 License. *)

(** The translation from the input AST to the internal one. *)

open Ast
open Common

module I = InputAst

let mk (type a) (node: a): a with_type =
  { node; typ = TAny }

let rec binders_of_pat p =
  let open I in
  match p with
  | PVar b ->
      [ b ]
  | PTuple ps
  | PCons (_, ps) ->
      KList.map_flatten binders_of_pat ps
  | PRecord fields ->
      KList.map_flatten binders_of_pat (snd (List.split fields))
  | PConstant _
  | PUnit
  | PBool _ ->
      []

let width_of_equality = function
  | TInt w -> Some w
  | TBool -> Some K.Bool
  | TQualified ([ "Prims" ], ("int" | "nat" | "pos")) -> Some K.CInt
  | _ -> None

let rec mk_decl = function
  | I.DFunction (cc, flags, n, t, name, binders, body) ->
      let body =
        if List.mem WipeBody flags then
          with_type TAny (EAbort (None, Some "noextract flag"))
        else
          mk_expr body
      in
      DFunction (cc, flags, 0, n, mk_typ t, name, mk_binders binders, body)
  | I.DTypeAlias (name, flags, n, t) ->
      DType (name, flags, 0, n, Abbrev (mk_typ t))
  | I.DGlobal (flags, name, n, t, e) ->
      DGlobal (flags, name, n, mk_typ t, mk_expr e)
  | I.DTypeFlat (name, flags, n, fields) ->
      DType (name, flags, 0, n, Flat (mk_tfields_opt fields))
  | I.DExternal (cc, flags, name, t) ->
      DExternal (cc, flags, 0, 0, name, mk_typ t, [])
  | I.DExternal2 (cc, flags, name, t, arg_names) ->
      DExternal (cc, flags, 0, 0, name, mk_typ t, arg_names)
  | I.DTypeVariant (name, flags, n, branches) ->
      DType (name, flags, 0, n,
        Variant (List.map (fun (ident, fields) -> ident, mk_tfields fields) branches))
  | I.DTypeAbstractStruct name ->
      DType (name, [], 0, 0, Forward FStruct)
  | I.DUntaggedUnion (name, flags, n, branches) ->
      DType (name, flags, 0, n, Union (List.map (fun (f, t) -> f, mk_typ t) branches))

and mk_binders bs =
  List.map mk_binder bs

and mk_binder { I.name; typ; mut } =
  Helpers.fresh_binder ~mut name (mk_typ typ)

and mk_tfields fields =
  List.map (fun (name, (field, mut)) -> name, (mk_typ field, mut)) fields

and mk_tfields_opt fields =
  List.map (fun (name, (field, mut)) -> Some name, (mk_typ field, mut)) fields

and mk_fields fields =
  List.map (fun (name, field) -> Some name, mk_expr field) fields

and mk_constant (w, s) =
  let module T = struct exception Error end in
  let rec skip_zeroes i =
    if i = String.length s then
      i
    else if s.[i] = '0' then
      skip_zeroes (i + 1)
    else begin
      skip_digits i;
      i
    end
  and skip_digits i =
    if i = String.length s then
      ()
    else if not ('0' <= s.[i] && s.[i] <= '9') then
      raise T.Error
    else
      skip_digits (i + 1)
  in
  if String.length s = 0 then
    w, s
  else
    try
      let i = skip_zeroes 0 in
      w, if i = String.length s then "0" else String.sub s i (String.length s - i)
    with T.Error ->
      w, s

and mk_typ = function
  | I.TInt x ->
      TInt x
  | I.TBuf t ->
      TBuf (mk_typ t, false)
  | I.TConstBuf t ->
      TBuf (mk_typ t, true)
  | I.TUnit ->
      TUnit
  | I.TQualified lid ->
      TQualified lid
  | I.TBool ->
      TBool
  | I.TAny ->
      TAny
  | I.TArrow (t1, t2) ->
      TArrow (mk_typ t1, mk_typ t2)
  | I.TBound i ->
      TBound i
  | I.TApp (lid, ts) ->
      TApp (lid, List.map mk_typ ts)
  | I.TTuple ts ->
      TTuple (List.map mk_typ ts)
  | I.TArray (t, c) ->
      TArray (mk_typ t, mk_constant c)

and mk_expr = function
  | I.EBound i ->
      mk (EBound i)
  | I.EQualified lid ->
      mk (EQualified lid)
  | I.EConstant k ->
      mk (EConstant (mk_constant k))
  | I.EUnit ->
      mk (EUnit)
  | I.EString s ->
      mk (EString s)

  | I.EApp (I.ETApp (I.EQualified ([ "LowStar"; "Monotonic"; "Buffer" ], "mnull"), [ t; _; _ ]), [ I.EUnit ])
  | I.EApp (I.ETApp (I.EQualified ([ "LowStar"; "Buffer" ], "null"), [ t ]), [ I.EUnit ])
  | I.EApp (I.ETApp (I.EQualified ([ "LowStar"; "ConstBuffer" ], "null"), [ t ]), [ I.EUnit ])
  | I.EApp (I.ETApp (I.EQualified ([ "Steel"; "Reference" ], "null"), [ t ]), [ I.EUnit ])
  | I.EApp (I.ETApp (I.EQualified ([ "C"; "Nullity" ], "null"), [ t ]), [ I.EUnit ])
  | I.EBufNull t ->
      { node = EBufNull; typ = TBuf (mk_typ t, false) }

  | I.EApp (I.ETApp (I.EQualified ( [ "LowStar"; "Monotonic"; "Buffer" ], "is_null"), [ t; _; _ ]), [ e ])
  | I.EApp (I.ETApp (I.EQualified ( [ "Steel"; "Reference" ], "is_null"), [ t ]), [ e ]) ->
      mk (EApp (mk (EPolyComp (K.PEq, TBuf (mk_typ t, false))), [
        mk_expr e;
        { node = EBufNull; typ = TBuf (mk_typ t, false) }]))

  | I.EApp (e, es) ->
      mk (EApp (mk_expr e, List.map mk_expr es))
  | I.ETApp (I.EOp ((K.Eq | K.Neq as op), _), [ t ]) ->
      let c = match op with K.Eq -> K.PEq | K.Neq -> K.PNeq | _ -> assert false in
      mk (EPolyComp (c, mk_typ t))
  | I.ETApp (e, es) ->
      mk (ETApp (mk_expr e, [], List.map mk_typ es))
  | I.ELet (b, e1, e2) ->
      mk (ELet (mk_binder b, mk_expr e1, mk_expr e2))
  | I.EIfThenElse (e1, e2, e3) ->
      mk (EIfThenElse (mk_expr e1, mk_expr e2, mk_expr e3))
  | I.EWhile (e1, e2) ->
      mk (EWhile (mk_expr e1, mk_expr e2))
  | I.ESequence es ->
      mk (ESequence (List.map mk_expr es))
  | I.EAssign (e1, e2) ->
      mk (EAssign (mk_expr e1, mk_expr e2))
  | I.EBufCreate (l, e1, e2) ->
      mk (EBufCreate (l, mk_expr e1, mk_expr e2))
  | I.EBufCreateNoInit (l, e2) ->
      mk (EBufCreate (l, Helpers.any, mk_expr e2))
  | I.EBufCreateL (l, es) ->
      mk (EBufCreateL (l, List.map mk_expr es))
  | I.EBufRead (e1, e2) ->
      mk (EBufRead (mk_expr e1, mk_expr e2))
  | I.EBufWrite (e1, e2, e3) ->
      mk (EBufWrite (mk_expr e1, mk_expr e2, mk_expr e3))
  | I.EBufFill (e1, e2, e3) ->
      mk (EBufFill (mk_expr e1, mk_expr e2, mk_expr e3))
  | I.EBufSub (e1, e2) ->
      mk (EBufSub (mk_expr e1, mk_expr e2))
  | I.EBufDiff (e1, e2) ->
      mk (EBufDiff (mk_expr e1, mk_expr e2))
  | I.EBufBlit (e1, e2, e3, e4, e5) ->
      mk (EBufBlit (mk_expr e1, mk_expr e2, mk_expr e3, mk_expr e4, mk_expr e5))
  | I.EBufFree e ->
      mk (EBufFree (mk_expr e))
  | I.EMatch (e1, bs) ->
      mk (EMatch (Checked, mk_expr e1, mk_branches bs))
  | I.EOp (op, w) ->
      mk (EOp (op, w))
  | I.ECast (e1, t) ->
      mk (ECast (mk_expr e1, mk_typ t))
  | I.EPushFrame ->
      mk EPushFrame
  | I.EPopFrame ->
      mk EPopFrame
  | I.EBool b ->
      mk (EBool b)
  | I.EAny ->
      mk EAny
  | I.EAbort ->
      mk (EAbort (None, None))
  | I.EAbortS s ->
      mk (EAbort (None, Some s))
  | I.EAbortT (s, t) ->
      { node = EAbort (Some (mk_typ t), Some s); typ = mk_typ t }
  | I.EReturn e ->
      mk (EReturn (mk_expr e))
  | I.EFlat (tname, fields) ->
      { node = EFlat (mk_fields fields); typ = mk_typ tname }
  | I.EField (tname, e, field) ->
      let e = { (mk_expr e) with typ = mk_typ tname } in
      mk (EField (e, field))
  | I.ETuple es ->
      mk (ETuple (List.map mk_expr es))
  | I.ECons (lid, id, es) ->
      { node = ECons (id, List.map mk_expr es); typ = mk_typ lid }
  | I.EFun (bs, e, t) ->
      mk (EFun (mk_binders bs, mk_expr e, mk_typ t))
  | I.EComment (before, e, after) ->
      mk (EComment (before, mk_expr e, after))
  | I.EStandaloneComment s ->
      mk (EStandaloneComment s)
  | I.EAddrOf e ->
      mk (EAddrOf (mk_expr e))

and mk_branches branches =
  List.map mk_branch branches

and mk_branch (pat, body) =
  (* This performs on-the-fly conversion to the proper multi-binder
   * representation. *)
  let binders = mk_binders (binders_of_pat pat) in
  binders, mk_pat (List.rev binders) pat, mk_expr body

and mk_pat binders pat =
  let rec mk_pat = function
  | I.PUnit ->
      mk PUnit
  | I.PBool b ->
      mk (PBool b)
  | I.PVar b ->
      mk (PBound (KList.index (fun b' -> b'.node.name = b.I.name) binders))
  | I.PTuple pats ->
      mk (PTuple (List.map mk_pat pats))
  | I.PCons (id, pats) ->
      mk (PCons (id, List.map mk_pat pats))
  | I.PRecord fields ->
      mk (PRecord (List.map (fun (field, pat) ->
        field, mk_pat pat
      ) fields))
  | I.PConstant k ->
      mk (PConstant (mk_constant k))
  in
  mk_pat pat

and mk_files files =
  List.map mk_program files

and mk_program (name, decls) =
  name, List.map mk_decl decls

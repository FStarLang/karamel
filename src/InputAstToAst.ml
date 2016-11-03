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
  | PUnit
  | PBool _ ->
      []

let rec mk_decl = function
  | I.DFunction (cc, flags, t, name, binders, body) ->
      let body =
        if List.exists ((=) NoExtract) flags then
          with_type TAny EAbort
        else
          mk_expr body
      in
      DFunction (cc, flags, mk_typ t, name, mk_binders binders, body)
  | I.DTypeAlias (name, n, t) ->
      DType (name, n, Abbrev (mk_typ t))
  | I.DGlobal (flags, name, t, e) ->
      DGlobal (flags, name, mk_typ t, mk_expr e)
  | I.DTypeFlat (name, n, fields) ->
      DType (name, n, Flat (mk_tfields_opt fields))
  | I.DExternal (cc, name, t) ->
      DExternal (cc, name, mk_typ t)
  | I.DTypeVariant (name, n, branches) ->
      DType (name, n,
        Variant (List.map (fun (ident, fields) -> ident, mk_tfields fields) branches))

and mk_binders bs =
  List.map mk_binder bs

and mk_binder { I.name; typ; mut } =
  fresh_binder ~mut name (mk_typ typ)

and mk_tfields fields =
  List.map (fun (name, (field, mut)) -> name, (mk_typ field, mut)) fields

and mk_tfields_opt fields =
  List.map (fun (name, (field, mut)) -> Some name, (mk_typ field, mut)) fields

and mk_fields fields =
  List.map (fun (name, field) -> Some name, mk_expr field) fields

and mk_typ = function
  | I.TInt x ->
      TInt x
  | I.TBuf t ->
      TBuf (mk_typ t)
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
  | I.TZ ->
      TZ
  | I.TBound i ->
      TBound i
  | I.TApp (lid, ts) ->
      TApp (lid, List.map mk_typ ts)
  | I.TTuple ts ->
      TTuple (List.map mk_typ ts)

and mk_expr = function
  | I.EBound i ->
      mk (EBound i)
  | I.EQualified lid ->
      mk (EQualified lid)
  | I.EConstant k ->
      mk (EConstant k)
  | I.EUnit ->
      mk (EUnit)
  | I.EApp (e, es) ->
      mk (EApp (mk_expr e, List.map mk_expr es))
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
  | I.EBufBlit (e1, e2, e3, e4, e5) ->
      mk (EBufBlit (mk_expr e1, mk_expr e2, mk_expr e3, mk_expr e4, mk_expr e5))
  | I.EMatch (e1, bs) ->
      mk (EMatch (mk_expr e1, mk_branches bs))
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
      mk EAbort
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
  in
  mk_pat pat

and mk_files files =
  List.map mk_program files

and mk_program (name, decls) =
  name, List.map mk_decl decls

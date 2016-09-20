(** The translation from the input AST to the internal one. *)

open Ast

module I = InputAst

let rec mk_decl = function
  | I.DFunction (t, name, binders, body) ->
      DFunction (mk_typ t, name, mk_binders binders, mk_expr body)
  | I.DTypeAlias (name, t) ->
      DTypeAlias (name, mk_typ t)
  | I.DGlobal (name, t, e) ->
      DGlobal (name, mk_typ t, mk_expr e)
  | I.DTypeFlat (name, fields) ->
      DTypeFlat (name, mk_tfields fields)
  | I.DExternal (name, t) ->
      DExternal (name, mk_typ t)

and mk_binders bs =
  List.map mk_binder bs

and mk_binder { I.name; typ; mut } =
  fresh_binder ~mut name (mk_typ typ)

and mk_tfields fields =
  List.map (fun (name, (field, mut)) -> name, (mk_typ field, mut)) fields

and mk_fields fields =
  List.map (fun (name, field) -> name, mk_expr field) fields

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
  | I.EBufCreate (e1, e2) ->
      mk (EBufCreate (mk_expr e1, mk_expr e2))
  | I.EBufCreateL es ->
      mk (EBufCreateL (List.map mk_expr es))
  | I.EBufRead (e1, e2) ->
      mk (EBufRead (mk_expr e1, mk_expr e2))
  | I.EBufWrite (e1, e2, e3) ->
      mk (EBufWrite (mk_expr e1, mk_expr e2, mk_expr e3))
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
      { node = EFlat (mk_fields fields); mtyp = TQualified tname }
  | I.EField (tname, e, field) ->
      let e = { (mk_expr e) with mtyp = TQualified tname } in
      mk (EField (e, field))

and mk node =
  { node; mtyp = TAny }

and mk_branches branches =
  List.map mk_branch branches

and mk_branch (pat, body) =
  mk_pat pat, mk_expr body

and mk_pat = function
  | I.PUnit ->
      PUnit
  | I.PBool b ->
      PBool b
  | I.PVar b ->
      PVar (mk_binder b)

and mk_files files =
  List.map mk_program files

and mk_program (name, decls) =
  name, List.map mk_decl decls

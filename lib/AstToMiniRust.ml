(* Low* to Rust backend *)

module StringMap = Map.Make(String)


(* Types *)

let borrow_kind_of_bool b: MiniRust.borrow_kind =
  if b (* const *) then
    Shared
  else
    Mut

let rec translate_type (t: Ast.typ): MiniRust.typ =
  match t with
  | TInt w -> Constant w
  | TBool -> Constant Bool
  | TUnit -> Unit
  | TAny -> failwith "unexpected: no casts in Low* -> Rust"
  | TBuf (t, b) -> Ref (borrow_kind_of_bool b, Slice (translate_type t))
  | TArray (t, c) -> Array (translate_type t, int_of_string (snd c))
  | TQualified _ -> failwith "TODO: TQualified"
  | TArrow _ -> failwith "TODO: TArrow"
  | TApp _ -> failwith "TODO: TApp"
  | TBound _ -> failwith "TODO: TBound"
  | TTuple _ -> failwith "TODO: TTuple"
  | TAnonymous _ -> failwith "unexpected: we don't compile data types going to Rust"


(* Environments *)

type env = {
  decls: MiniRust.typ StringMap.t;
  vars: MiniRust.binding list;
}

let empty = { decls = StringMap.empty; vars = [] }

let push env (x, t) = { env with vars = (x, t) :: env.vars }

let lookup env v = List.nth env.vars v


(* Expressions *)

let translate_lid (m, n) = m @ [ n ]

(* Translate an expression, and take the annotated original type to be the
   expected type. *)
let rec translate_expr (env: env) (e: Ast.expr): MiniRust.expr =
  translate_expr_with_type env e (translate_type e.typ)

and translate_array (env: env) (init: Ast.expr): MiniRust.expr * MiniRust.typ =
  match init.node with
  | EBufCreate (Stack, init, ({ node = EConstant (_, s); _ } as len)) ->
      Array (Repeat (translate_expr env init, translate_expr env len)),
      Array (translate_type init.typ, int_of_string s)
  | EBufCreateL (Stack, es) ->
      Array (List (List.map (translate_expr env) es)),
      Array (translate_type init.typ, List.length es)
  | EBufCreate (_, init, len) ->
      VecNew (Repeat (translate_expr env init, translate_expr env len)),
      Vec (translate_type init.typ)
  | EBufCreateL (_, es) ->
      VecNew (List (List.map (translate_expr env) es)),
      Vec (translate_type init.typ)
  | _ ->
      failwith "unexpected: non-bufcreate expression"

(* However, generally, we will have a type provided by the context that may
   necessitate the insertion of conversions *)
and translate_expr_with_type (env: env) (e: Ast.expr) (t_ret: MiniRust.typ): MiniRust.expr =
  match e.node with
  | EOpen _ ->
      failwith "unexpected: EOpen"
  | EBound v ->
      let _, t = lookup env v in
      begin match t, t_ret with
      | (Vec _ | Array _), Slice _ ->
          Borrow (Mut, (Place (Var v)))
      | Constant UInt32, Constant SizeT ->
          As (Place (Var v), t_ret)
      | _, _ ->
          if t = t_ret then
            Place (Var v)
          else
            failwith "type mismatch"
      end
  | EOp (o, _) ->
      Operator o
  | EQualified lid ->
      Name (translate_lid lid)
  | EConstant c ->
      Constant c
  | EUnit ->
      Unit
  | EBool b ->
      Constant (Bool, string_of_bool b)
  | EString _ ->
      failwith "TODO: strings"
  | EAny ->
      failwith "unexpected: no casts in Low* -> Rust"
  | EAbort (_, s) ->
      Panic (Stdlib.Option.value ~default:"" s)
  | EIgnore _ ->
      failwith "unexpected: EIgnore"
  | EApp (e, es) ->
      Call (translate_expr env e, List.map (translate_expr env) es)
  | ETApp _ ->
      failwith "TODO: ETApp"
  | EPolyComp _ ->
      failwith "unexpected: EPolyComp"
  | ELet (b, ({ node = EBufCreate _ | EBufCreateL _; _ } as init), e2) ->
      let e1, t = translate_array env init in
      let binding = b.node.name, t in
      let env = push env binding in
      Let (binding, e1, translate_expr_with_type env e2 t_ret)
  | ELet (b, e1, e2) ->
      let e1 = translate_expr env e1 in
      let t = translate_type b.typ in
      let binding = b.node.name, t in
      let env = push env binding in
      Let (binding, e1, translate_expr_with_type env e2 t_ret)
  | EFun _ ->
      failwith "unexpected: EFun"
  | EIfThenElse (e1, e2, e3) ->
      let e1 = translate_expr env e1 in
      let e2 = translate_expr_with_type env e2 t_ret in
      let e3 = if e3.node = EUnit then Some (translate_expr_with_type env e3 t_ret) else None in
      IfThenElse (e1, e2, e3)
  | ESequence _ ->
      failwith "unexpected: ESequence"
  | EAssign (e1, e2) ->
      Assign (translate_place env e1, translate_expr env e2)
  | EBufCreate _ ->
      failwith "unexpected: EBufCreate"
  | EBufCreateL _ ->
      failwith "unexpected: EBufCreateL"
  | EBufRead _ ->
      Place (translate_place env e)
  | EBufWrite (e1, e2, e3) ->
      let p1 = translate_place env e1 in
      let e2 = translate_expr env e2 in
      let e3 = translate_expr env e3 in
      Assign (Index (p1, e2), e3)
  | EBufSub _ ->
      failwith "unexpected: EBufSub"
  | EBufDiff _ ->
      failwith "unexpected: EBufDiff"
  | EBufBlit _ ->
      failwith "TODO: EBufBlit"
  | EBufFill _ ->
      failwith "TODO: EBufFill"
  | EBufFree _ ->
      failwith "unexpected: EBufFree"
  | EBufNull ->
      VecNew (List [])
  | EPushFrame ->
      failwith "unexpected: EPushFrame"
  | EPopFrame ->
      failwith "unexpected: EPopFrame"

  | ETuple _ ->
      failwith "TODO: ETuple"
  | EMatch _ ->
      failwith "TODO: EMatch"
  | ECons _ ->
      failwith "TODO: ECons"

  | ESwitch _ ->
      failwith "TODO: ESwitch"
  | EEnum _ ->
      failwith "TODO: EEnum"
  | EFlat _ ->
      failwith "TODO: EFlat"
  | EField _ ->
      failwith "TODO: EField"
  | EBreak ->
      failwith "TODO: EBreak"
  | EContinue ->
      failwith "TODO: EContinue"
  | EReturn _ ->
      failwith "TODO: EReturn"
  | EWhile _ ->
      failwith "TODO: EWhile"
  | EFor _ ->
      failwith "TODO: EFor"
  | ECast _ ->
      failwith "TODO: ECast"
  | EComment _ ->
      failwith "TODO: EComment"
  | EStandaloneComment _ ->
      failwith "TODO: EStandaloneComment"
  | EAddrOf e ->
      Borrow (Mut, translate_expr env e)

and translate_place env (e: Ast.expr): MiniRust.place =
  match e.node with
  | EBound v ->
      Var v
  | EBufRead (e1, e2) ->
      let p1 = translate_place env e1 in
      let e2 = translate_expr env e2 in
      Index (p1, e2)
  | _ ->
      failwith "unexpected: not a place"

let translate_decl env (d: Ast.decl) =
  match d with
  | Ast.DFunction (_cc, _flags, _n, t, name, args, body) ->
      KPrint.bprintf "Ast.DFunction (%a)\n" PrintAst.Ops.plid name;
      let parameters = List.map (fun b -> b.Ast.node.Ast.name, translate_type b.typ) args in
      let env = List.fold_left push env parameters in
      let body = translate_expr env body in
      let return_type = translate_type t in
      let name = translate_lid name in
      Some (MiniRust.Function { parameters; return_type; body; name })
  | Ast.DGlobal (_, name, _, _, _) ->
      KPrint.bprintf "TODO: Ast.DGlobal (%a)\n" PrintAst.Ops.plid name;
      None
  | Ast.DExternal (_, _, _, name, _, _) ->
      KPrint.bprintf "TODO: Ast.DExternal (%a)\n" PrintAst.Ops.plid name;
      None
  | Ast.DType (name, _, _, _) ->
      KPrint.bprintf "TODO: Ast.DType (%a)\n" PrintAst.Ops.plid name;
      None

let translate_files files =
  List.map (fun (f, decls) ->
    f, KList.filter_map (translate_decl empty) decls
  ) files

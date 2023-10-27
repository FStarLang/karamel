(* Low* to Rust backend *)

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

type env = {
  decls: typ StringMap.t;
  vars: MiniRust.binding list;
}

let push env x t = { env with vars = (x, t) :: env.vars }

(* Translate an expression, and take the annotated original type to be the
   expected type. *)
let rec translate_expr (env: env) (e: Ast.expr): expr =
  translate_expr_with_type env e (translate_type e.typ)

(* However, generally, we will have a type provided by the context that may
   necessitate the insertion of conversions *)
and translate_expr_with_type (env: env) (e: Ast.expr) (t_ret: typ): expr =
  match e.node with
  | EOpen _ ->
      failwith "unexpected: EOpen"
  | EBound v ->
      let _, t = lookup env v in
      begin match t, t_ret with
      | (Vec _ | Array _), Slice _ ->
          Ref (Mut, (Var v))
      | Constant UInt32, Constant USize ->
          As (Var v, t_ret)
      | _, _ ->
          if t = t_ret then
            Var v
          else
            failwith "type mismatch"
      end
  | EOp o ->
      Operator o
  | EQualified (m, n) ->
      Name (m @ [ n ])
  | EConstant c ->
      Constant c
  | EUnit ->
      Unit
  | EBool b ->
      Constant (b, Bool)
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
  | ELet (b, { node = EBufCreate _ | EBufCreateL _ as init; _ }, e2) ->
      let t, e = translate_array env init in
      let env = push env b.node.name t in
      translate_expr_with_type env e2 t_ret
  | ELet (b, e1, e2) ->
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
      Assign (translate_expr env e1, translate_expr env e2)
  | EBufCreate _ ->
      failwith "unexpected: EBufCreate"
  | EBufCreateL _ ->
      failwith "unexpected: EBufCreateL"
  | EBufRead _ ->
  | EBufWrite _ ->
  | EBufSub _ ->
  | EBufDiff _ ->
  | EBufBlit _ ->
  | EBufFill _ ->
  | EBufFree _ ->
      failwith "unexpected: EBufFree"
  | EBufNull ->
      Ref (Array (List []))
  | EPushFrame ->
      failwith "unexpected: EPushFrame"
  | EPopFrame ->
      failwith "unexpected: EPopFrame"

  | ETuple of expr list
  | EMatch of match_flavor * expr * branches
  | ECons of ident * expr list

  | ESwitch of expr * (switch_case * expr) list
  | EEnum of lident
  | EFlat of fields_e_opt
  | EField of expr * ident
  | EBreak
  | EContinue
  | EReturn of expr
  | EWhile of expr * expr
  | EFor of binder * expr * expr * expr * expr
  | ECast of expr * typ_wo
  | EComment of string * expr * string
  | EStandaloneComment of string
  | EAddrOf of expr


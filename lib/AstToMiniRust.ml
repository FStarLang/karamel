(* Low* to Rust backend *)

module NameMap = Map.Make(struct
  type t = MiniRust.name
  let compare = compare
end)


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
  | TArrow _ ->
      let t, ts = Helpers.flatten_arrow t in
      Function (List.map translate_type ts, translate_type t)
  | TApp _ -> failwith "TODO: TApp"
  | TBound _ -> failwith "TODO: TBound"
  | TTuple _ -> failwith "TODO: TTuple"
  | TAnonymous _ -> failwith "unexpected: we don't compile data types going to Rust"


(* Environments *)

type env = {
  decls: MiniRust.typ NameMap.t;
  vars: MiniRust.binding list;
}

let empty = { decls = NameMap.empty; vars = [] }

let push env (x, t) = { env with vars = (x, t) :: env.vars }

let push_global env name t = { env with decls = NameMap.add name t env.decls }

let lookup env v = List.nth env.vars v

let lookup_global env name =
  NameMap.find name env.decls


(* Expressions *)

let translate_lid (m, n) = m @ [ n ]

(* Helpers *)

module H = struct

  let plus e1 e2: MiniRust.expr = Call (Operator Add, [ e1; e2 ])
  let range_with_len start len: MiniRust.expr = Range (Some start, Some (plus start len), false)

end

(* Translate an expression, and take the annotated original type to be the
   expected type. *)
let rec translate_expr (env: env) (e: Ast.expr): MiniRust.expr =
  translate_expr_with_type env e (translate_type e.typ)

and translate_array (env: env) is_toplevel (init: Ast.expr): MiniRust.expr * MiniRust.typ =
  let to_array = function
    | Common.Stack -> true
    | Eternal -> is_toplevel
    | Heap -> false
  in

  match init.node with
  | EBufCreate (lifetime, e_init, ({ node = EConstant (_, s); _ } as len)) ->
      let t = translate_type (Helpers.assert_tbuf_or_tarray init.typ) in
      let l = int_of_string s in
      let e_init = MiniRust.Repeat (translate_expr env e_init, translate_expr env len) in
      if to_array lifetime then
        Array e_init, Array (t, l)
      else
        VecNew e_init, Vec t
  | EBufCreateL (lifetime, es) ->
      let t = translate_type (Helpers.assert_tbuf_or_tarray init.typ) in
      let l = List.length es in
      let e_init = MiniRust.List (List.map (translate_expr env) es) in
      if to_array lifetime then
        Array e_init, Array (t, l)
      else
        VecNew e_init, Vec t
  | _ ->
      failwith "unexpected: non-bufcreate expression"

(* However, generally, we will have a type provided by the context that may
   necessitate the insertion of conversions *)
and translate_expr_with_type (env: env) (e: Ast.expr) (t_ret: MiniRust.typ): MiniRust.expr =
  let possibly_convert x t: MiniRust.expr =
    begin match t, t_ret with
    | (MiniRust.Vec _ | Array _), Ref (k, Slice _) ->
        Borrow (k, x)
    | Constant UInt32, Constant SizeT ->
        As (x, Constant SizeT)
    | _, _ ->
        if t = t_ret then
          x
        else
          Warn.fatal_error "type mismatch;\n  t=%s\n  t_ret=%s\n  x=%s"
            (MiniRust.show_typ t) (MiniRust.show_typ t_ret)
            (MiniRust.show_expr x)
    end
  in

  match e.node with
  | EOpen _ ->
      failwith "unexpected: EOpen"
  | EBound v ->
      let _, t = lookup env v in
      possibly_convert (Place (Var v)) t
  | EOp (o, _) ->
      Operator o
  | EQualified lid ->
      let name = translate_lid lid in
      begin try
        let t = lookup_global env name in
        possibly_convert (Name name) t
      with Not_found ->
        (* External -- TODO: make sure external definitions are properly added
           to the scope *)
        Name name
      end
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
      let e1, t = translate_array env false init in
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
      let e1 = translate_expr env e1 in
      let e2 = translate_expr env e2 in
      let e3 = translate_expr env e3 in
      Assign (Index (e1, e2), e3)
  | EBufSub (e1, e2) ->
      (* TODO: static analysis to collect and do something smarter with
         slice_at_mut *)
      let e1 = translate_expr env e1 in
      let e2 = translate_expr env e2 in
      Borrow (Mut, Place (Index (e1, Range (Some e2, None, false))))
  | EBufDiff _ ->
      failwith "unexpected: EBufDiff"
  | EBufBlit (src, src_index, dst, dst_index, len) ->
      let src = translate_expr env src in
      let src_index = translate_expr env src_index in
      let dst = translate_expr env dst in
      let dst_index = translate_expr env dst_index in
      let len = translate_expr env len in
      MethodCall (
        Place (Index (dst, H.range_with_len dst_index len)),
        [ "copy_from_slice" ],
        [ Borrow (Shared, Place (Index (src, H.range_with_len src_index len))) ])
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
  | EFor (b, e_start, e_test, e_incr, e_body) ->
      let e_end = match e_test.node, e_incr.node with
        | EApp ({ node = EOp (Lt, _); _ }, [ { node = EBound 0; _ }; e_end ]),
          EAssign ({ node = EBound 0; _ },
          { node = EApp ({ node = EOp ((Add | AddW), _); _ }, [
            { node = EBound 0; _ };
            { node = EConstant (_, "1"); _ } ]); _ }) ->
              e_end
        | _ ->
            Warn.fatal_error "Unsupported loop:\n e_test=%a\n e_incr=%a\n"
              PrintAst.Ops.pexpr e_test
              PrintAst.Ops.pexpr e_incr
      in
      let binding = b.node.name, translate_type b.typ in
      let e_start = translate_expr env e_start in
      let e_end = translate_expr env e_end in
      let e_body = translate_expr (push env binding) e_body in
      For (binding, Range (Some e_start, Some e_end, false), e_body)
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
      let e1 = translate_expr env e1 in
      let e2 = translate_expr env e2 in
      Index (e1, e2)
  | _ ->
      Warn.fatal_error "unexpected: not a place: %a" PrintAst.Ops.pexpr e

let translate_decl env (d: Ast.decl) =
  match d with
  | Ast.DFunction (_cc, _flags, _n, t, name, args, body) ->
      if Options.debug "rs" then
        KPrint.bprintf "Ast.DFunction (%a)\n" PrintAst.Ops.plid name;
      let parameters = List.map (fun b -> b.Ast.node.Ast.name, translate_type b.typ) args in
      let env0 = List.fold_left push env parameters in
      let body = translate_expr env0 body in
      let return_type = translate_type t in
      let name = translate_lid name in
      let env = push_global env name (Function (snd (List.split parameters), return_type)) in
      Some (env, MiniRust.Function { parameters; return_type; body; name })
  | Ast.DGlobal (_, name, _, t, e) ->
      let body, typ = match e.node with
        | EBufCreate _ | EBufCreateL _ ->
            KPrint.bprintf "array!!!\n";
            translate_array env true e
        | _ ->
            translate_expr env e, translate_type t
      in
      if Options.debug "rs" then
        KPrint.bprintf "Ast.DGlobal (%a: %s)\n" PrintAst.Ops.plid name (MiniRust.show_typ typ);
      let name = translate_lid name in
      let env = push_global env name typ in
      Some (env, MiniRust.Constant { name; typ; body })
  | Ast.DExternal (_, _, _, name, _, _) ->
      KPrint.bprintf "TODO: Ast.DExternal (%a)\n" PrintAst.Ops.plid name;
      None
  | Ast.DType (name, _, _, _) ->
      KPrint.bprintf "TODO: Ast.DType (%a)\n" PrintAst.Ops.plid name;
      None

let translate_files files =
  let _, files = List.fold_left (fun (env, files) (f, decls) ->
    let env, decls = List.fold_left (fun (env, decls) d ->
      match translate_decl env d with
      | Some (env, d) ->
          env, d :: decls
      | None ->
          env, decls
    ) (env, []) decls in
    let decls = List.rev decls in
    env, (f, decls) :: files
  ) (empty, []) files in
  List.rev files

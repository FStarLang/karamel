open CMinor

module W = Wasm
module K = Constant

module StringMap = Map.Make(String)

type env = {
  funcs: int StringMap.t;
  stack: size list
}

let empty = {
  funcs = StringMap.empty;
  stack = []
}

let grow env locals = {
  env with
  stack = env.stack @ locals
}

let dummy_pos =
  W.Source.({ file = ""; line = 0; column = 0 })

let dummy_region =
  W.Source.({ left = dummy_pos; right = dummy_pos })

let dummy_phrase what =
  W.Source.({ at = dummy_region; it = what })

let mk_var x = dummy_phrase (Int32.of_int x)

let mk_value_type = function
  | I32 ->
      W.Types.I32Type
  | I64 ->
      W.Types.I64Type

let sized_op (s: size) op =
  match s with
  | I32 ->
      W.Values.I32 op
  | I64 ->
      W.Values.I64 op

let mk_lit s lit =
  match s with
  | I32 ->
      dummy_phrase (W.Values.I32 (Int32.of_string lit))
  | I64 ->
      dummy_phrase (W.Values.I64 (Int64.of_string lit))

let mk_binop (o: K.op) =
  let open W.Ast.IntOp in
  match o with
  | K.Add | K.AddW ->
      Some Add
  | K.Sub | K.SubW ->
      Some Sub
  | K.Div | K.DivW ->
      failwith "todo div"
  | K.Mult | K.MultW ->
      Some Mul
  | K.Mod ->
      failwith "todo mod"
  | K.BOr | K.Or ->
      Some Or
  | K.BAnd | K.And ->
      Some And
  | K.BXor | K.Xor ->
      Some Xor
  | K.BShiftL
  | K.BShiftR ->
      failwith "todo shift"
  | _ ->
      None

let is_binop (o: K.op) =
  mk_binop o <> None

let mk_cmpop (o: K.op) =
  let open W.Ast.IntOp in
  match o with
  | K.Eq ->
      Some Eq
  | K.Neq ->
      Some Ne
  | K.BNot | K.Not ->
      failwith "todo not (zero minus?)"
  | K.Lt
  | K.Lte
  | K.Gt
  | K.Gte ->
      failwith "todo comparisons"
  | _ ->
      None

let is_cmpop (o: K.op) =
  mk_cmpop o <> None

let rec mk_expr env (e: expr): W.Ast.instr list =
  match e with
  | Var i ->
      [ dummy_phrase (W.Ast.GetLocal (mk_var i)) ]

  | Constant (s, lit) ->
      [ dummy_phrase (W.Ast.Const (mk_lit s lit)) ]

  | Call (Op (s, o), [ e1; e2 ]) when is_binop o ->
      mk_expr env e1 @
      mk_expr env e2 @
      [ dummy_phrase (W.Ast.Binary (sized_op s (Option.must (mk_binop o)))) ]

  | Call (Op (s, o), [ e1; e2 ]) when is_cmpop o ->
      mk_expr env e1 @
      mk_expr env e2 @
      [ dummy_phrase (W.Ast.Compare (sized_op s (Option.must (mk_cmpop o)))) ]

  | Call (Qualified name, es) ->
      let index = StringMap.find name env.funcs in
      KList.map_flatten (mk_expr env) es @
      [ dummy_phrase (W.Ast.Call (mk_var index)) ]

  | _ ->
      failwith "not implemented"

let rec mk_stmt env (stmt: stmt): W.Ast.instr list =
  match stmt with
  | Return e ->
      Option.map_or (mk_expr env) e [] @
      [ dummy_phrase W.Ast.Return ]

  | IfThenElse (e, b1, b2) ->
      (* I assume that the [stack_type] is the *return* type of the
       * if-then-else... since conditionals are always in statement position
       * then it must be the case that the blocks return nothing. *)
      mk_expr env e @
      [ dummy_phrase (W.Ast.If ([ W.Types.I32Type ], mk_stmts env b1, mk_stmts env b2)) ]

  | Assign (Var i, e) ->
      mk_expr env e @
      [ dummy_phrase (W.Ast.SetLocal (mk_var i)) ]

  | _ ->
      failwith "Not implemented"

and mk_stmts env (stmts: stmt list): W.Ast.instr list =
  KList.map_flatten (mk_stmt env) stmts

let mk_func_type { args; ret; _ } =
  W.Types.( FuncType (
    List.map mk_value_type args,
    List.map mk_value_type ret))

let mk_func env i { args; locals; body; _ } =
  let env = grow env args in
  let env = grow env locals in

  let body = mk_stmts env body in
  let locals = List.map mk_value_type locals in
  let ftype = mk_var i in
  dummy_phrase W.Ast.({ locals; ftype; body })

let mk_module (name, decls): string * W.Ast.module_ =
  (* Filter the functions *)
  let funcs = KList.filter_map (function
    | Function f -> Some f
    | _ -> None
  ) decls in

  (* Build our map from function *names* to their global index *)
  let env = KList.fold_lefti (fun i env { name; _ } ->
    { env with funcs = StringMap.add name i env.funcs }
  ) empty funcs in

  (* And translate them *)
  let types = List.map mk_func_type funcs in
  let exports = KList.filter_map (fun { name; public; _ } ->
    if public then
      Some (dummy_phrase W.Ast.({
        name;
        ekind = dummy_phrase W.Ast.FuncExport;
        item = mk_var (StringMap.find name env.funcs)
      }))
    else
      None
  ) funcs in
  let funcs = List.mapi (mk_func env) funcs in


  let module_ = dummy_phrase W.Ast.({
    empty_module with
    funcs;
    types;
    exports
  }) in
  name, module_

let mk_files files =
  List.map mk_module files

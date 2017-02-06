open CFlat

module W = Wasm
module K = Constant

module StringMap = Map.Make(String)

(** Our environments map top-level function identifiers to their index in the
 * global table. They also keep a map of each local stack index to its size. *)
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

let size_at env i =
  List.nth env.stack i

(** We don't make any effort (yet) to keep track of positions even though Wasm
 * really wants us to. *)
let dummy_pos =
  W.Source.({ file = ""; line = 0; column = 0 })

let dummy_region =
  W.Source.({ left = dummy_pos; right = dummy_pos })

let dummy_phrase what =
  W.Source.({ at = dummy_region; it = what })

(** A bunch of helpers *)
let mk_var x = dummy_phrase (Int32.of_int x)

let mk_type = function
  | I32 ->
      W.Types.I32Type
  | I64 ->
      W.Types.I64Type

let mk_value s x =
  match s with
  | I32 ->
      W.Values.I32 x
  | I64 ->
      W.Values.I64 x

let mk_lit w lit =
  match w with
  | K.Int32 | K.UInt32 ->
      dummy_phrase (W.Values.I32 (Int32.of_string lit))
  | K.Int64 | K.UInt64 ->
      dummy_phrase (W.Values.I64 (Int64.of_string lit))
  | _ ->
      failwith "mk_lit"

(** Binary operations take a width and an operation, in order to pick the right
 * flavor of signed vs. unsigned operation *)
let mk_binop (w, o) =
  let open W.Ast.IntOp in
  match o with
  | K.Add | K.AddW ->
      Some Add
  | K.Sub | K.SubW ->
      Some Sub
  | K.Div | K.DivW ->
      (* Fortunately, it looks like FStar.Int*, C and Wasm all adopt the
       * "rounding towards zero" behavior. Phew! *)
      if K.is_signed w then
        Some DivS
      else
        Some DivU
  | K.Mult | K.MultW ->
      Some Mul
  | K.Mod ->
      if K.is_signed w then
        Some RemS
      else
        Some RemU
  | K.BOr | K.Or ->
      Some Or
  | K.BAnd | K.And ->
      Some And
  | K.BXor | K.Xor ->
      Some Xor
  | K.BShiftL ->
      Some Shl
  | K.BShiftR ->
      if K.is_signed w then
        Some ShrS
      else
        Some ShrU
  | _ ->
      None

let is_binop (o: K.width * K.op) =
  mk_binop o <> None

let mk_cmpop (w, o) =
  let open W.Ast.IntOp in
  match o with
  | K.Eq ->
      Some Eq
  | K.Neq ->
      Some Ne
  | K.BNot | K.Not ->
      failwith "todo not (zero minus?)"
  | K.Lt ->
      if K.is_signed w then
        Some LtS
      else
        Some LtU
  | K.Lte ->
      if K.is_signed w then
        Some LeS
      else
        Some LeU
  | K.Gt ->
      if K.is_signed w then
        Some GtS
      else
        Some GtU
  | K.Gte ->
      if K.is_signed w then
        Some GeS
      else
        Some GeU
  | _ ->
      None

let is_cmpop (o: K.width * K.op) =
  mk_cmpop o <> None


(** There are two types of conversions. The first one is load/store conversions,
 * that require resizing from a possibly larger local size to the right operand
 * size. *)
let resize orig dest =
  match orig, dest with
  | I64, I32 ->
      [ dummy_phrase (W.Ast.Convert (W.Values.I64 W.Ast.IntOp.WrapI64)) ]
  | I32, I64 ->
      [ dummy_phrase (W.Ast.Convert (W.Values.I32 W.Ast.IntOp.ExtendUI32)) ]
  | _ ->
      []

let truncate w =
  let open K in
  match w with
  | UInt32 | Int32 | UInt64 | Int64 ->
      []
  | _ ->
      failwith "todo: truncate"

let rec mk_callop2 env (w, o) e1 e2 =
  (* TODO: check special byte semantics C / WASM *)
  let size = size_of_width w in
  mk_expr env e1 @
  mk_expr env e2 @
  if is_binop (w, o) then
    [ dummy_phrase (W.Ast.Binary (mk_value size (Option.must (mk_binop (w, o))))) ] @
    truncate w
  else if is_cmpop (w, o) then
    [ dummy_phrase (W.Ast.Compare (mk_value size (Option.must (mk_cmpop (w, o))))) ] @
    truncate w
  else
    failwith "todo mk_callop2"

and mk_expr env (e: expr): W.Ast.instr list =
  match e with
  | Var (i, s) ->
      [ dummy_phrase (W.Ast.GetLocal (mk_var i)) ] @ resize (size_at env i) s

  | Constant (w, lit) ->
      [ dummy_phrase (W.Ast.Const (mk_lit w lit)) ]

  | CallOp (o, [ e1; e2 ]) ->
      mk_callop2 env o e1 e2

  | CallFunc (name, es) ->
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

  | Assign ((i, s), e) ->
      mk_expr env e @
      resize s (size_at env i) @
      [ dummy_phrase (W.Ast.SetLocal (mk_var i)) ]

  | _ ->
      failwith "Not implemented"

and mk_stmts env (stmts: stmt list): W.Ast.instr list =
  KList.map_flatten (mk_stmt env) stmts

let mk_func_type { args; ret; _ } =
  W.Types.( FuncType (
    List.map mk_type args,
    List.map mk_type ret))

let mk_func env i { args; locals; body; _ } =
  let env = grow env args in
  let env = grow env locals in

  let body = mk_stmts env body in
  let locals = List.map mk_type locals in
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

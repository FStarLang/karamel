open CFlat
open CFlat.Sizes

module W = Wasm
module K = Constant

module StringMap = Map.Make(String)

(** Our environments map top-level function identifiers to their index in the
 * global table. They also keep a map of each local stack index to its size. *)
type env = {
  funcs: int StringMap.t;
  globals: int StringMap.t;
  stack: size list
}

let empty = {
  funcs = StringMap.empty;
  globals = StringMap.empty;
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

(** Dealing with size mismatches *)
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

let mk_int32 i =
  dummy_phrase (W.Values.I32 i)

let mk_int64 i =
  dummy_phrase (W.Values.I64 i)

let mk_lit w lit =
  match w with
  | K.Int32 | K.UInt32 ->
      mk_int32 (Int32.of_string lit)
  | K.Int64 | K.UInt64 ->
      mk_int64 (Int64.of_string lit)
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

(** Memory management. We use a bump-pointer allocator called the "highwater
 * mark". One can read it (grows the stack by one); grow it by the specified
 * offset (shrinks the stack by one); restore a value into it (also shrinks the
 * stack by one). *)
let i32_mul =
  [ dummy_phrase (W.Ast.Binary (mk_value I32 W.Ast.IntOp.Mul)) ]

let read_highwater =
  [ dummy_phrase (W.Ast.GetGlobal (mk_var 0)) ]

let write_highwater =
  [ dummy_phrase (W.Ast.SetGlobal (mk_var 0)) ]

let grow_highwater =
  read_highwater @
  i32_mul @
  write_highwater

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
  | Var i ->
      [ dummy_phrase (W.Ast.GetLocal (mk_var i)) ]

  | Constant (w, lit) ->
      [ dummy_phrase (W.Ast.Const (mk_lit w lit)) ]

  | CallOp (o, [ e1; e2 ]) ->
      mk_callop2 env o e1 e2

  | CallFunc (name, es) ->
      let index = StringMap.find name env.funcs in
      KList.map_flatten (mk_expr env) es @
      [ dummy_phrase (W.Ast.Call (mk_var index)) ]

  | BufCreate (Common.Stack, n_elts, elt_size) ->
      (* TODO semantics discrepancy the size is a uint32 both in Low* and Wasm
       * but Low* talks about the number of elements while Wasm talks about the
       * number of bytes *)
      read_highwater @
      mk_expr env n_elts @
      [ dummy_phrase (W.Ast.Const (mk_int32 (Int32.of_int (bytes_in elt_size)))) ] @
      i32_mul @
      grow_highwater

  | _ ->
      failwith ("not implemented (expr); got: " ^ show_expr e)

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

  | Assign (i, e) ->
      mk_expr env e @
      [ dummy_phrase (W.Ast.SetLocal (mk_var i)) ]

  | _ ->
      failwith ("not implemented (stmt); got: " ^ show_stmt stmt)

and mk_stmts env (stmts: stmt list): W.Ast.instr list =
  KList.map_flatten (mk_stmt env) stmts

let mk_func_type { args; ret; _ } =
  W.Types.( FuncType (
    List.map mk_type args,
    List.map mk_type ret))

let mk_func env { args; locals; body; name; _ } =
  let i = StringMap.find name env.funcs in
  let env = grow env args in
  let env = grow env locals in

  let body = mk_stmts env body in
  let locals = List.map mk_type locals in
  let ftype = mk_var i in
  dummy_phrase W.Ast.({ locals; ftype; body })

let mk_global env size body =
  let body = mk_expr env body in
  dummy_phrase W.Ast.({
    gtype = W.Types.GlobalType (mk_type size, W.Types.Mutable);
    value = dummy_phrase body
  })

let mk_module (name, decls): string * W.Ast.module_ =
  (* Assign functions and global their index in the table *)
  let rec assign env f g = function
    | Function { name; _ } :: tl ->
        let env = { env with funcs = StringMap.add name f env.funcs } in
        assign env (f + 1) g tl
    | Global (name, _, _, _) :: tl -> 
        let env = { env with globals = StringMap.add name g env.globals } in
        assign env f (g + 1) tl
    | _ :: tl ->
        assign env f g tl
    | [] ->
        env
  in
  (* The first global is the highwater mark *)
  let env = assign empty 0 1 decls in

  (* Generate types for the function declarations. There is the invariant that
   * the function at index i in the function table has type i in the types
   * table. *)
  let types = KList.filter_map (function
    | Function f ->
        Some (mk_func_type f)
    | _ ->
        None
  ) decls in
  let exports = KList.filter_map (function
    | Function { public; name; _ } when public ->
        Some (dummy_phrase W.Ast.({
          name;
          ekind = dummy_phrase W.Ast.FuncExport;
          item = mk_var (StringMap.find name env.funcs)
        }))
    | Global (name, _, _, public) when public ->
        Some (dummy_phrase W.Ast.({
          name;
          ekind = dummy_phrase W.Ast.GlobalExport;
          item = mk_var (StringMap.find name env.globals)
        }))
    | _ ->
        None
  ) decls in
  let funcs = KList.filter_map (function
    | Function f ->
        Some (mk_func env f)
    | _ ->
        None
  ) decls in
  let globals =
    (* Highwater mark *)
    dummy_phrase W.Ast.({
      gtype = W.Types.GlobalType (mk_type I32, W.Types.Mutable);
      value = dummy_phrase [
        dummy_phrase (W.Ast.Const (mk_int32 0l))
      ]
    }) ::
    KList.filter_map (function
      | Global (_, size, body, _) ->
          Some (mk_global env size body)
      | _ ->
          None
    ) decls
  in

  let module_ = dummy_phrase W.Ast.({
    empty_module with
    funcs;
    types;
    globals;
    exports
  }) in
  name, module_

let mk_files files =
  List.map mk_module files

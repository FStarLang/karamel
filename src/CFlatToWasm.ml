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
  stack: size list;
  n_args: int
}

let empty = {
  funcs = StringMap.empty;
  globals = StringMap.empty;
  stack = [];
  n_args = 0
}

let grow env locals = {
  env with
  stack = env.stack @ locals
}

let size_at env i =
  List.nth env.stack i

(** We don't make any effort (yet) to keep track of positions even though Wasm
 * really wants us to. *)
let dummy_phrase what =
  W.Source.(what @@ no_region)

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

let mk_const c =
  [ dummy_phrase (W.Ast.Const c) ]

let mk_lit w lit =
  match w with
  | K.Int32 | K.UInt32 | K.Bool ->
      mk_int32 (Int32.of_string lit)
  | K.Int64 | K.UInt64 ->
      mk_int64 (Int64.of_string lit)
  | _ ->
      failwith "mk_lit"

let todo w =
  match w with
  | K.Int8 | K.Int16 -> failwith "todo"
  | _ -> ()

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
      todo w;
      (* Fortunately, it looks like FStar.Int*, C and Wasm all adopt the
       * "rounding towards zero" behavior. Phew! *)
      if K.is_signed w then
        Some DivS
      else
        Some DivU
  | K.Mult | K.MultW ->
      Some Mul
  | K.Mod ->
      todo w;
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
      todo w;
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
      todo w;
      if K.is_signed w then
        Some LtS
      else
        Some LtU
  | K.Lte ->
      todo w;
      if K.is_signed w then
        Some LeS
      else
        Some LeU
  | K.Gt ->
      todo w;
      if K.is_signed w then
        Some GtS
      else
        Some GtU
  | K.Gte ->
      todo w;
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

let i32_add =
  [ dummy_phrase (W.Ast.Binary (mk_value I32 W.Ast.IntOp.Add)) ]

let i32_and =
  [ dummy_phrase (W.Ast.Binary (mk_value I32 W.Ast.IntOp.And)) ]

let i32_sub =
  [ dummy_phrase (W.Ast.Binary (mk_value I32 W.Ast.IntOp.Sub)) ]

let i32_not =
  mk_const (mk_int32 Int32.min_int) @
  [ dummy_phrase (W.Ast.Binary (mk_value I32 W.Ast.IntOp.Sub)) ]

let i32_zero =
  mk_const (mk_int32 Int32.zero)

let i32_one =
  mk_const (mk_int32 Int32.one)

let mk_unit =
  i32_zero

let mk_drop =
  [ dummy_phrase W.Ast.Drop ]

(* Wasm lacks two crucial instructions: dup (to duplicate the operand at the
 * top of the stack) and swap (to swap the two topmost operands). There are some
 * macros, such as grow_highwater (or 16/8-bit arithmetic), that we want to
 * expand at the last minute (since they use some very low-level Wasm concepts).
 * Therefore, as a convention, every function frame has four "scratch" locals;
 * the first two of size I64; the last two of size I32. The Wasm register
 * allocator will take care of optimizing all of that. *)
let dup32 env =
  [ dummy_phrase (W.Ast.TeeLocal (mk_var (env.n_args + 2)));
    dummy_phrase (W.Ast.GetLocal (mk_var (env.n_args + 2))) ]

let dup64 env =
  [ dummy_phrase (W.Ast.TeeLocal (mk_var (env.n_args + 0)));
    dummy_phrase (W.Ast.GetLocal (mk_var (env.n_args + 0))) ]

let swap32 env =
  [ dummy_phrase (W.Ast.SetLocal (mk_var (env.n_args + 2)));
    dummy_phrase (W.Ast.SetLocal (mk_var (env.n_args + 3)));
    dummy_phrase (W.Ast.GetLocal (mk_var (env.n_args + 2)));
    dummy_phrase (W.Ast.GetLocal (mk_var (env.n_args + 3))) ]

let swap64 env =
  [ dummy_phrase (W.Ast.SetLocal (mk_var (env.n_args + 0)));
    dummy_phrase (W.Ast.SetLocal (mk_var (env.n_args + 1)));
    dummy_phrase (W.Ast.GetLocal (mk_var (env.n_args + 0)));
    dummy_phrase (W.Ast.GetLocal (mk_var (env.n_args + 1))) ]

(* The highwater mark denotes the top of the stack (bump-pointer allocation).
 * Since it needs to be shared across modules, and since Wasm does not support
 * exported, mutable globals, we use the first word of the (shared) memory for
 * that purpose. *)
let read_highwater =
  i32_zero @
  [ dummy_phrase W.Ast.(Load { ty = mk_type I32; align = 0; offset = 0l; sz = None }) ]

let write_highwater env =
  i32_zero @
  swap32 env @
  [ dummy_phrase W.Ast.(Store { ty = mk_type I32; align = 0; offset = 0l; sz = None }) ]

let grow_highwater env =
  read_highwater @
  i32_add @
  write_highwater env

(** Dealing with size mismatches *)

(** The delicate question is how to handle integer types < 32 bits. Two options
 * for signed integers:
 * - keep the most significant bit as the sign bit (i.e; the 32nd bit), and use
 *   the remaining lowest n-1 bits; this means that operations that need to care
 *   about the sign (shift-right, division, remainder) can be builtin Wasm
 *   operations; then, assuming we want to replicate the C semantics:
 *   + signed to larger signed = no-op
 *   + signed to smaller signed = mask & shift sign bit
 *   + unsigned to smaller unsigned = mask
 *   + unsigned to larger unsigned = no-op
 *   + signed to smaller unsigned = mask
 *   + signed to equal or greater unsigned = shift sign bit
 *   + unsigned to smaller or equal signed = mask & shift sign bit
 *   + unsigned to larger signed = no-op
 * - use the lowest n bits and re-implement "by hand" operations that require us
 *   to care about the sign
 *   + signed to larger signed = sign-extension
 *   + signed to smaller signed = mask
 *   + unsigned to smaller unsigned = mask
 *   + unsigned to larger unsigned = no-op
 *   + signed to smaller unsigned = mask
 *   + signed to greater unsigned = sign-extension
 *   + unsigned to smaller or equal signed = mask
 *   + unsigned to larger signed = no-op
 *)
let mk_mask w =
  let open K in
  match w with
  | UInt32 | Int32 | UInt64 | Int64 | UInt | Int ->
      []
  | UInt16 | Int16 ->
      mk_const (mk_int32 0xffffl) @
      i32_and
  | UInt8 | Int8 ->
      mk_const (mk_int32 0xffl) @
      i32_and
  | _ ->
      []

let mk_cast w_from w_to =
  let open K in
  match w_from, w_to with
  | (UInt8 | UInt16 | UInt32), (Int64 | UInt64 | Int | UInt) ->
      (* Zero-padding, C semantics. That's 12 cases. *)
      [ dummy_phrase (W.Ast.Convert (W.Values.I32 W.Ast.IntOp.ExtendUI32)) ]
  | Int32, (Int64 | UInt64 | Int | UInt) ->
      (* Sign-extend, then re-interpret, also C semantics. That's 12 more cases. *)
      [ dummy_phrase (W.Ast.Convert (W.Values.I32 W.Ast.IntOp.ExtendSI32)) ]
  | (Int64 | UInt64 | Int | UInt), (Int32 | UInt32) ->
      (* Truncate, still C semantics (famous last words?). That's 24 cases. *)
      [ dummy_phrase (W.Ast.Convert (W.Values.I64 W.Ast.IntOp.WrapI64)) ] @
      mk_mask w_to
  | (Int8 | UInt8), (Int8 | UInt8)
  | (Int16 | UInt16), (Int16 | UInt16)
  | (Int32 | UInt32), (Int32 | UInt32)
  | (Int64 | UInt64), (Int64 | UInt64) ->
      []
  | UInt8, (UInt16 | UInt32)
  | UInt16, UInt32 ->
      []
  | UInt16, UInt8
  | UInt32, (UInt16 | UInt8) ->
      mk_mask w_to
  | Bool, _ | _, Bool ->
      invalid_arg "mk_cast"
  | _ ->
      failwith "todo: signed cast conversions"


module Debug = struct

  let mark_size = 4

  (* Debugging conventions. We assume some scratch space at the beginning of the
   * memory; bytes 0..3 are the highwater mark, and bytes 4..127 are scratch space
   * to write in a zero-terminated string to be read by the (externally-provided)
   * debug function. This space may evolve to include more information. The debug
   * function is always the function imported first (to easily generate debugging
   * code). *)
  let default_imports = [
    dummy_phrase W.Ast.({
      module_name = "Kremlin";
      item_name = "debug";
      ikind = dummy_phrase (FuncImport (mk_var 0))
    })
  ]

  let default_types = [
    W.Types.FuncType ([], [])
  ]

  let store_char_at c addr =
    let c = Char.code c in
    mk_const (mk_int32 (Int32.of_int addr)) @
    mk_const (mk_int32 (Int32.of_int c)) @
    [ dummy_phrase W.Ast.(Store {
        ty = mk_type I32; align = 0; offset = 0l; sz = Some W.Memory.Mem8 })]

  let string s =
    if Options.debug "wasm-calls" then
      let l = String.length s in
      List.flatten (KList.make l (fun i -> store_char_at s.[i] (i + mark_size))) @
      store_char_at '\x00' (l + mark_size) @
      [ dummy_phrase (W.Ast.Call (mk_var 0)) ]
    else
      []

end

(** Actual translations *)
let rec mk_callop2 env (w, o) e1 e2 =
  (* TODO: check special byte semantics C / WASM *)
  let size = size_of_width w in
  mk_expr env e1 @
  mk_expr env e2 @
  if is_binop (w, o) then
    [ dummy_phrase (W.Ast.Binary (mk_value size (Option.must (mk_binop (w, o))))) ] @
    mk_mask w
  else if is_cmpop (w, o) then
    [ dummy_phrase (W.Ast.Compare (mk_value size (Option.must (mk_cmpop (w, o))))) ] @
    mk_mask w
  else
    failwith "todo mk_callop2"

and mk_size size =
  [ dummy_phrase (W.Ast.Const (mk_int32 (Int32.of_int (bytes_in size)))) ]

and mk_expr env (e: expr): W.Ast.instr list =
  match e with
  | Var i ->
      [ dummy_phrase (W.Ast.GetLocal (mk_var i)) ]

  | Constant (w, lit) ->
      mk_const (mk_lit w lit)

  | CallOp (o, [ e1; e2 ]) ->
      mk_callop2 env o e1 e2

  | CallFunc (name, es) ->
      let index =
        try StringMap.find name env.funcs
        with Not_found ->
          failwith ("not found: " ^ name)
      in
      KList.map_flatten (mk_expr env) es @
      [ dummy_phrase (W.Ast.Call (mk_var index)) ]

  | BufCreate (Common.Stack, n_elts, elt_size) ->
      (* TODO semantics discrepancy the size is a uint32 both in Low* and Wasm
       * but Low* talks about the number of elements while Wasm talks about the
       * number of bytes *)
      read_highwater @
      mk_expr env n_elts @
      mk_size elt_size @
      i32_mul @
      grow_highwater env

  | BufRead (e1, e2, size) ->
      (* github.com/WebAssembly/spec/blob/master/interpreter/spec/eval.ml#L189 *)
      mk_expr env e1 @
      mk_expr env e2 @
      mk_size size @
      i32_mul @
      i32_add @
      [ dummy_phrase W.Ast.(Load {
        (* the type we want on the operand stack *)
        ty = mk_type (if size = A64 then I64 else I32); 
        (* ignored *)
        align = 0;
        (* we've already done the multiplication ourselves *)
        offset = 0l;
        (* we store 32-bit integers in 32-bit slots, and smaller than that in
         * 32-bit slots as well, so no conversion M32 for us *)
        sz = match size with
          | A16 -> Some W.Memory.(Mem16, ZX)
          | A8 -> Some W.Memory.(Mem8, ZX)
          | _ -> None })]

  | BufSub (e1, e2, size) ->
      mk_expr env e1 @
      mk_expr env e2 @
      mk_size size @
      i32_mul @
      i32_add

  | Cast (e1, w_from, w_to) ->
      mk_expr env e1 @
      mk_cast w_from w_to

  | IfThenElse (e, b1, b2, s) ->
      let s = mk_type s in
      mk_expr env e @
      [ dummy_phrase (W.Ast.If ([ s ], mk_expr env b1, mk_expr env b2)) ]

  | Assign (i, e) ->
      mk_expr env e @
      [ dummy_phrase (W.Ast.SetLocal (mk_var i)) ] @
      mk_unit

  | BufWrite (e1, e2, e3, size) ->
      mk_expr env e1 @
      mk_expr env e2 @
      mk_size size @
      i32_mul @
      i32_add @
      mk_expr env e3 @
      [ dummy_phrase W.Ast.(Store {
        ty = mk_type (if size = A64 then I64 else I32); 
        align = 0;
        offset = 0l;
        sz = match size with
          | A16 -> Some W.Memory.Mem16
          | A8 -> Some W.Memory.Mem8
          | _ -> None })] @
      mk_unit

  | While (e, expr) ->
      [ dummy_phrase (W.Ast.Loop ([],
        mk_expr env e @
        i32_not @
        [ dummy_phrase (W.Ast.BrIf (mk_var 0)) ] @
        mk_expr env expr @
        mk_drop)) ] @
      mk_unit

  | Ignore _ ->
      mk_drop

  | Sequence es ->
      let es, e = KList.split_at_last es in
      List.flatten (List.map (fun e ->
        mk_expr env e @
        [ dummy_phrase W.Ast.Drop ]
      ) es) @
      mk_expr env e

  | PushFrame ->
      read_highwater @
      mk_unit

  | PopFrame ->
      write_highwater env @
      mk_unit

  | _ ->
      failwith ("not implemented; got: " ^ show_expr e)

let mk_func_type { args; ret; _ } =
  W.Types.( FuncType (
    List.map mk_type args,
    List.map mk_type ret))

let mk_func env { args; locals; body; name; _ } =
  let i = StringMap.find name env.funcs in
  let env = grow env args in
  let env = grow env locals in
  let env = { env with n_args = List.length args } in

  let body =
    Debug.string name @
    mk_expr env body
  in
  let locals = List.map mk_type locals in
  let ftype = mk_var i in
  dummy_phrase W.Ast.({ locals; ftype; body })

let mk_global env size body =
  let body = mk_expr env body in
  dummy_phrase W.Ast.({
    gtype = W.Types.GlobalType (mk_type size, W.Types.Immutable);
    value = dummy_phrase body
  })

let mk_module types imports (name, decls): string * W.Ast.module_ =
  (* Assign imports their index in the table *)
  let rec assign env i imports =
    let funcs = env.funcs in
    let open W.Ast in
    let open W.Source in
    match imports with
    | { it = { item_name; ikind = { it = FuncImport n; _ }; _ }; _ } :: tl ->
        let env = { env with funcs = StringMap.add item_name (Int32.to_int n.it) funcs } in
        assign env (i + 1) tl
    | _ :: tl ->
        assign env i tl
    | [] ->
        env
  in
  let env = assign empty 0 imports in

  (* Assign functions and globals their index in the table. Functions defined in
   * the current module come after imports in the "function index space". *)
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
  (* The first global is reserved for the highwater mark. *)
  let env = assign env (List.length types) 1 decls in

  (* Generate types for the function declarations. There is the invariant that
   * the function at index i in the function table has type i in the types
   * table. *)
  let types = types @ KList.filter_map (function
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

  let mtype = W.Types.MemoryType W.Types.({ min = 16l; max = None }) in
  let memories = [ ] in
  (* We import our memory; to be allocated by the caller. *)
  let imports = dummy_phrase W.Ast.({
    module_name = "Kremlin";
    item_name = "mem";
    ikind = dummy_phrase (MemoryImport mtype)
  }) :: imports in

  let module_ = dummy_phrase W.Ast.({
    empty_module with
    funcs;
    types;
    globals;
    exports;
    imports;
    memories
  }) in
  name, module_


(* Since the modules are already topologically sorted, we make each module
 * import all the exports from all the previous modules. [imports] is a list of
 * everything that been made visible so far... ideally, we should only import
 * things that we need. *)
let mk_files files =
  let _, _, modules = List.fold_left (fun (types, imports, modules) file ->
    let module_name, _ = file in
    let module_ = mk_module (List.rev types) (List.rev imports) file in
    let offset = List.length types in
    let open W.Ast in
    let open W.Source in
    let _, types, imports = List.fold_left (fun (offset, types, imports) x ->
      match x.it with
      | { name; ekind = { it = FuncExport; _ }; item } ->
          offset + 1,
          List.nth (snd module_).it.types (Int32.to_int item.it) :: types,
          dummy_phrase {
            module_name;
            item_name = name;
            ikind = dummy_phrase (FuncImport (mk_var offset))
          } :: imports
      | { name; ekind = { it = GlobalExport; _ }; item } ->
          let t = List.nth (snd module_).it.globals (Int32.to_int item.it) in
          offset,
          types,
          dummy_phrase {
            module_name;
            item_name = name;
            ikind = dummy_phrase (GlobalImport t.it.gtype)
          } :: imports
      | _ ->
          failwith "todo/import"
    ) (offset, types, imports) (snd module_).it.exports in
    types, imports, module_ :: modules
  ) (Debug.default_types, Debug.default_imports, []) files in
  List.rev modules

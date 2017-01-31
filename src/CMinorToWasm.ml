open CMinor

module W = Wasm

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

let mk_stmt _env (stmt: stmt) =
  match stmt with
  | Return None ->
      dummy_phrase W.Ast.Return
  | _ ->
      failwith "Not implemented"

let mk_func_type { args; ret; _ } =
  W.Types.( FuncType (
    List.map mk_value_type args,
    List.map mk_value_type ret))

let mk_func env i { args; locals; body; _ } =
  let env = grow env args in
  let env = grow env locals in

  let body = List.map (mk_stmt env) body in
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
  let funcs = List.mapi (mk_func env) funcs in

  let module_ = dummy_phrase W.Ast.({
    empty_module with
    funcs;
    types
  }) in
  name, module_

let mk_files files =
  List.map mk_module files

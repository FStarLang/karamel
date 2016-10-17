open CStar

module W = Wasm

let dummy_pos =
  W.Source.({ file = ""; line = 0; column = 0 })

let dummy_region =
  W.Source.({ left = dummy_pos; right = dummy_pos })

let dummy_phrase what =
  W.Source.({ at = dummy_region; it = what })

exception Not_implemented

let mk_stmt (stmt: stmt) =
  match stmt with
  | Return None ->
      dummy_phrase W.Ast.Return
  | _ ->
      raise Not_implemented

let mk_stmts (block: block) =
  List.map mk_stmt block

let mk_decl (decl: decl) =
  match decl with
  | Function (_ret_t, _name, _binders, body) ->
      begin try
        let body = mk_stmts body in
        Some (dummy_phrase W.Ast.({ ftype = dummy_phrase 0l; locals = []; body }))
      with Not_implemented ->
        None
      end

  | Global _ ->
      None

  | Type _ ->
      None

  | External _ ->
      None

let mk_module (files: (string * program) list): W.Ast.module_ =
  let funcs = KList.map_flatten (fun (_, decls) ->
    KList.filter_map mk_decl decls
  ) files in
  dummy_phrase W.Ast.({
    empty_module with
    funcs
  })

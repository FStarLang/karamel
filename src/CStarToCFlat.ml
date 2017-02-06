(** Going from CStar to CFlat *)

module CS = CStar
module CF = CFlat

module StringMap = Map.Make(String)

type size = CFlat.size =
  I32 | I64

let size_of (t: CS.typ): size =
  match t with
  | CS.Int w ->
      CF.size_of_width w
  | CS.Pointer _ ->
      I32
  | CS.Void  ->
      invalid_arg "size_of: only for expression types"
  | CS.Qualified _ ->
      failwith "not implemented"
  | CS.Array _ ->
      I32
  | CS.Function (_,_,_) ->
      failwith "not implemented"
  | CS.Bool ->
      I32
  | CS.Z
  | CS.Struct _
  | CS.Enum _
  | CS.Union _ ->
      failwith "not implemented"

let max s1 s2 =
  match s1, s2 with
  | I32, I32 -> I32
  | _ -> I64

type locals = size list

let merge (l1: locals) (l2: locals) =
  let rec aux acc l1 l2 =
    match l1, l2 with
    | s1 :: l1, s2 :: l2 ->
        aux (max s1 s2 :: acc) l1 l2
    | [], l2 ->
        List.rev_append acc l2
    | l1, [] ->
        List.rev_append acc l1
  in
  aux [] l1 l2

type env = {
  vars: (string * (int * size)) list;
}

let empty = {
  vars = []
}

let bind (env: env) (binder: CS.binder): env * CF.var =
  let i = List.length env.vars in {
    vars = (binder.CS.name, (i, size_of binder.CS.typ)) :: env.vars
  }, i

let extend env binder =
  fst (bind env binder)

let find env v =
  List.assoc v env.vars

let rec translate_expr (env: env) (e: CS.expr): CF.expr =
  match e with
  | CS.Var v ->
      let i, _ = find env v in
      CF.Var i

  | CS.Call (CS.Op (o, w), es) ->
      CF.CallOp ((w, o), List.map (translate_expr env) es)

  | CS.Call (CS.Qualified ident, es) ->
      CF.CallFunc (ident, List.map (translate_expr env) es)

  | CS.Constant (w, lit) ->
      CF.Constant (w, lit)

  | _ ->
      failwith "not implemented (expr)"

let assert_var = function
  | CF.Var i -> i
  | _ -> invalid_arg "assert_var"

let rec translate_stmts (env: env) (stmts: CS.stmt list): env * CF.stmt list =
  match stmts with
  | [] ->
      env, []

  | CS.Decl (binder, e) :: stmts ->
      let e = translate_expr env e in
      let env, v = bind env binder in
      let env, stmts = translate_stmts env stmts in
      env, CF.Assign (v, e) :: stmts

  | CS.IfThenElse (e, stmts1, stmts2) :: stmts ->
      let e = translate_expr env e in
      let env, stmts1 = translate_stmts env stmts1 in
      let env, stmts2 = translate_stmts env stmts2 in
      let env, stmts = translate_stmts env stmts in
      env, CF.IfThenElse (e, stmts1, stmts2) :: stmts

  | CS.Return e :: stmts ->
      let env, stmts = translate_stmts env stmts in
      env, CF.Return (Option.map (translate_expr env) e) :: stmts

  | CS.Abort :: _ ->
      env, [ CF.Abort ]

  | CS.Ignore e :: stmts ->
      let env, stmts = translate_stmts env stmts in
      env, CF.Ignore (translate_expr env e) :: stmts

  | CS.While (e, block) :: stmts ->
      let env, block = translate_stmts env block in
      let env, stmts = translate_stmts env stmts in
      env, CF.While (translate_expr env e, block) :: stmts

  | CS.Assign (e, e') :: stmts ->
      let env, stmts = translate_stmts env stmts in
      let e = translate_expr env e in
      let e' = translate_expr env e' in
      env, CF.Assign (assert_var e, e') :: stmts

  | CS.Copy (dst, t, src) :: stmts ->
      let elt_size, elt_count =
        match t with
        | CS.Array (t, e) -> size_of t, translate_expr env e
        | _ -> failwith "Copy / Array?"
      in
      let dst = translate_expr env dst in
      let src = translate_expr env src in
      let env, stmts = translate_stmts env stmts in
      env, CF.Copy (dst, src, elt_size, elt_count) :: stmts

  | CS.Switch _ :: _ ->
      failwith "todo: switch"

  | CS.BufWrite (e1, e2, e3) :: stmts ->
      let env, stmts = translate_stmts env stmts in
      let e1 = translate_expr env e1 in
      let e2 = translate_expr env e2 in
      let e3 = translate_expr env e3 in
      env, CF.BufWrite (e1, e2, e3) :: stmts

  | CS.BufBlit (e1, e2, e3, e4, e5) :: stmts ->
      let env, stmts = translate_stmts env stmts in
      let e1 = translate_expr env e1 in
      let e2 = translate_expr env e2 in
      let e3 = translate_expr env e3 in
      let e4 = translate_expr env e4 in
      let e5 = translate_expr env e5 in
      env, CF.BufBlit (e1, e2, e3, e4, e5) :: stmts

  | CS.BufFill (e1, e2, e3) :: stmts ->
      let env, stmts = translate_stmts env stmts in
      let e1 = translate_expr env e1 in
      let e2 = translate_expr env e2 in
      let e3 = translate_expr env e3 in
      env, CF.BufFill (e1, e2, e3) :: stmts

  | CS.PushFrame :: stmts ->
      let env, stmts = translate_stmts env stmts in
      env, CF.PushFrame :: stmts

  | CS.PopFrame :: stmts ->
      let env, stmts = translate_stmts env stmts in
      env, CF.PopFrame :: stmts

  | CS.Comment _ :: stmts ->
      translate_stmts env stmts

let translate_decl (d: CS.decl): CF.decl =
  match d with
  | CS.Function (_, flags, ret, name, args, body) ->
      let public = not (List.exists ((=) Common.Private) flags) in
      let env = List.fold_left extend empty args in
      let env, body = translate_stmts env body in
      let ret = [ size_of ret ] in
      let args, locals =
        KList.split_at (List.length args) (List.map (fun (_, (_, s)) -> s) env.vars)
      in
      CF.(Function { name; args; ret; locals; body; public })

  | _ ->
      failwith "not implemented (decl)"

let translate_module (name, decls) =
  name, KList.filter_map (fun d ->
    try
      Some (translate_decl d)
    with e ->
      (* Remove when everything starts working *)
      KPrint.beprintf "[C*ToC-] Couldn't translate %s:\n%s\n%s\n"
        (CS.ident_of_decl d) (Printexc.to_string e)
        (Printexc.get_backtrace ());
      None
  ) decls

let translate_files files =
  List.map translate_module files

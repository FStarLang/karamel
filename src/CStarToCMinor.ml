(** Going from CStar to CMinor *)

open Constant

module CS = CStar
module CM = CMinor

module StringMap = Map.Make(String)

type size = CMinor.size =
  I32 | I64

let size_of_width (w: width) =
  match w with
  | UInt64 | Int64 | UInt | Int ->
      I64
  | _ ->
      I32

let size_of (t: CS.typ): size =
  match t with
  | CS.Int w ->
      size_of_width w
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
  map: int StringMap.t;
  size: int;
}

let empty = {
  map = StringMap.empty;
  size = 0;
}

let extend (env: env) (binder: CS.binder): env * size =
  let env = {
    map = StringMap.add binder.CS.name env.size env.map;
    size = env.size + 1
  } in
  env, size_of binder.CS.typ

let grow (env: env) (size: int): env =
  { env with size = env.size + size }

let rec translate_expr (env: env) (e: CS.expr): CM.expr =
  match e with
  | CS.Var i ->
      CM.Var (StringMap.find i env.map)

  | CS.Call (e, es) ->
      CM.Call (translate_expr env e, List.map (translate_expr env) es)

  | CS.Constant (w, lit) ->
      CM.Constant (size_of_width w, lit)

  | CS.Op (o, w) ->
      CM.Op (size_of_width w, o)

  | CS.Qualified i ->
      CM.Qualified i

  | _ ->
      failwith "not implemented (expr)"

let rec translate_stmts (env: env) (stmts: CS.stmt list): locals * CM.stmt list =
  match stmts with
  | [] ->
      [], []

  | CS.Decl (binder, e) :: stmts ->
      let e = translate_expr env e in
      let v = CM.Var env.size in
      let env, local = extend env binder in
      let locals, stmts = translate_stmts env stmts in
      local :: locals, CM.Assign (v, e) :: stmts

  | CS.IfThenElse (e, stmts1, stmts2) :: stmts ->
      let e = translate_expr env e in
      let locals1, stmts1 = translate_stmts env stmts1 in
      let locals2, stmts2 = translate_stmts env stmts2 in
      let locals_ite = merge locals1 locals2 in
      let locals, stmts = translate_stmts (grow env (List.length locals_ite)) stmts in
      locals_ite @ locals, CM.IfThenElse (e, stmts1, stmts2) :: stmts

  | CS.Return e :: stmts ->
      let locals, stmts = translate_stmts env stmts in
      locals, CM.Return (Option.map (translate_expr env) e) :: stmts

  | _ ->
      failwith "not implemented (stmts)"

let translate_decl (d: CS.decl): CM.decl =
  match d with
  | CS.Function (_, _, ret, name, args, body) ->
      let env, args = List.fold_left (fun (env, args) binder ->
        let env, arg = extend env binder in
        env, arg :: args
      ) (empty, []) args in
      let locals, body = translate_stmts env body in
      let ret = [ size_of ret ] in
      CM.(Function { name; args; ret; locals; body })

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

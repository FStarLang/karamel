(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 and MIT Licenses. *)

open Ast
open Clang.Ast
module K = Constant

type env = {
  (* Variables in the context *)
  vars: string list
}

let empty_env = {vars = []}

let add_var env var = {vars = var :: env.vars }

let find_var env var = EBound (KList.index (fun x -> x = var) env.vars)

let extract_width = function | TInt w -> w | _ -> failwith "not an integer type"

let get_id_name (dname: declaration_name) = match dname with
  | IdentifierName s -> s
  | _ -> failwith "only supporting identifiers"

let translate_typ_name = function
  | "uint32_t" -> Helpers.uint32
  | _ -> failwith "unsupported name"

let rec translate_typ (typ: qual_type) = match typ.desc with
  | Pointer typ -> TBuf (translate_typ typ, false)
  | Typedef {name; _} -> get_id_name name |> translate_typ_name
  | BuiltinType Void -> TUnit
  | BuiltinType _ -> failwith "builtin type"
  | _ -> failwith "not pointer type"

let translate_expr (env: env) (t: typ) (e: expr) = match e.desc with
  | IntegerLiteral (Int n) -> EConstant (extract_width t, string_of_int n)
  | DeclRef {name; _} -> get_id_name name |> find_var env
  | _ -> failwith "translate_expr"

let translate_vardecl (env: env) (vdecl: var_decl_desc) : env * binder * Ast.expr =
  let name = vdecl.var_name in
  let typ = translate_typ vdecl.var_type in
  match vdecl.var_init with
  | None -> failwith "Variable declarations without definitions are not supported"
  | Some e -> add_var env name, Helpers.fresh_binder name typ, Ast.with_type typ (translate_expr env typ e)

let rec translate_stmt (env: env) (s: stmt_desc) : expr' = match s with
  | Compound l -> begin match l with
    | [] -> EUnit
    | hd :: tl -> match hd.desc with
      | Decl [{desc = Var vdecl; _ }] ->
          let env', b, e = translate_vardecl env vdecl in
          ELet (b, e, Ast.with_type TUnit (translate_stmt env' (Compound tl)))
      | Decl [_] -> failwith "This decl is not a var declaration"
      | Decl _ -> failwith "multiple decls"
      | stmt -> ELet (
        Helpers.sequence_binding (),
        Ast.with_type TUnit (translate_stmt env stmt),
        Ast.with_type TUnit (translate_stmt (add_var env "_") (Compound tl)))
   end
  | _ -> EUnit

let translate_param (p: parameter) : binder * string =
  let p = p.desc in
  let typ = translate_typ p.qual_type in
  (* Not handling default expressions for function parameters *)
  assert (p.default = None);
  Helpers.fresh_binder p.name typ, p.name

let translate_fundecl (fdecl: function_decl) =
  let name = get_id_name fdecl.name in
  let ret_type = translate_typ fdecl.function_type.result in
  let args, vars = match fdecl.function_type.parameters with
    | None -> [], []
    | Some params ->
        (* Not handling variadic parameters *)
        assert (not (params.variadic));
        List.map translate_param params.non_variadic |> List.split
  in
  (* To adopt a DeBruijn representation, the list must be reversed to
   have the last binder as the first element of the environment *)
  let env = {vars = List.rev vars} in
  let body = match fdecl.body with | None -> EUnit | Some s -> translate_stmt env s.desc in
  let decl = Ast.(DFunction (None, [], 0, 0, ret_type, ([], name), args, with_type ret_type body)) in
  KPrint.bprintf "Resulting decl %a\n" PrintAst.pdecl decl;
  decl


let translate_decl (decl: decl) = match decl.desc with
  | Function fdecl ->
    let name = get_id_name fdecl.name in
    Printf.printf "Translating function %s\n" name;
    if name = "test" then (* || name = "quarter_round" then *)
      Some (translate_fundecl fdecl)
    else None
  | _ -> None

let read_file () =
  let ast = parse_file "test.c" in
  (* Format.printf "@[%a@]@." (Refl.pp [%refl: Clang.Ast.translation_unit] []) ast; *)
  Printf.printf "Trying file %s\n" ast.desc.filename;
  let decls = List.filter_map translate_decl ast.desc.items in
  let files = ["test", decls] in
  let files = AstToMiniRust.translate_files files in
  let files = OptimizeMiniRust.cleanup_minirust files in
  let files = OptimizeMiniRust.infer_mut_borrows files in
  let files = OptimizeMiniRust.simplify_minirust files in
  OutputRust.write_all files


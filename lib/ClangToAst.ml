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

let extract_width = function | TInt w -> w | _ -> failwith "not an integer type"

let get_id_name (dname: declaration_name) = match dname with
  | IdentifierName s -> s
  | _ -> failwith "only supporting identifiers"

let translate_typ_name = function
  | "uint32_t" -> Helpers.uint32
  | _ -> failwith "unsupported name"

let translate_typ (typ: qual_type) = match typ.desc with
  | Pointer _ -> failwith "pointer type"
  | Typedef {name; _} -> get_id_name name |> translate_typ_name
  | _ -> failwith "not pointer type"

let translate_expr (t: typ) (e: expr) = match e.desc with
  | IntegerLiteral (Int n) -> EConstant (extract_width t, string_of_int n)
  | _ -> failwith "translate_expr"

let translate_vardecl (env: env) (vdecl: var_decl_desc) : env * binder * Ast.expr =
  let name = vdecl.var_name in
  let typ = translate_typ vdecl.var_type in
  match vdecl.var_init with
  | None -> failwith "Variable declarations without definitions are not supported"
  | Some e -> add_var env name, Helpers.fresh_binder name typ, Ast.with_type typ (translate_expr typ e)

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

let translate_fundecl (fdecl: function_decl) =
  let name = get_id_name fdecl.name in
  let body = match fdecl.body with | None -> EUnit | Some s -> translate_stmt empty_env s.desc in
  let decl = Ast.(DFunction (None, [], 0, 0, TUnit, ([], name), [], with_type TUnit body)) in
  KPrint.bprintf "Resulting decl %a\n" PrintAst.pdecl decl;
  ()


let translate_decl (decl: decl) = match decl.desc with
  | Function fdecl ->
    let name = get_id_name fdecl.name in
    Printf.printf "Translating function %s\n" name;
    if name = "test" || name = "quarter_round" then
      translate_fundecl fdecl
    else ()
  | _ -> ()

let read_file () =
  let ast = parse_file "test.c" in
  (* Format.printf "@[%a@]@." (Refl.pp [%refl: Clang.Ast.translation_unit] []) ast; *)
  Printf.printf "Trying file %s\n" ast.desc.filename;
  let _decls = List.map translate_decl ast.desc.items in
  ()


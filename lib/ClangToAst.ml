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

let get_id_name (dname: declaration_name) = match dname with
  | IdentifierName s -> s
  | _ -> failwith "only supporting identifiers"

let translate_binop (kind: Clang__Clang__ast.binary_operator_kind) : K.op = match kind with
  | Add -> Add
  (* TODO: How to distinguish between Xor and BXor? Likely need typing info from operands *)
  | Xor -> BXor
  | Or -> BOr
  | Shl -> BShiftL
  | Shr -> BShiftR
  | _ -> failwith "translate_binop"

let translate_typ_name = function
  | "uint32_t" -> Helpers.uint32
  | _ -> failwith "unsupported name"

let rec translate_typ (typ: qual_type) = match typ.desc with
  | Pointer typ -> TBuf (translate_typ typ, false)
  | Typedef {name; _} -> get_id_name name |> translate_typ_name
  | BuiltinType Void -> TUnit
  | BuiltinType UInt -> TInt UInt32 (* How to retrieve exact width? *)
  | BuiltinType Pointer -> failwith "builtin pointer"
  | BuiltinType _ -> failwith "builtin type"
  | _ -> failwith "not pointer type"

(* Translate expression [e], with expected type [t] *)
let rec translate_expr' (env: env) (t: typ) (e: expr) : expr' = match e.desc with
  | IntegerLiteral (Int n) -> EConstant (Helpers.assert_tint t, string_of_int n)
  | BoolLiteral _ -> failwith "translate_expr: bool literal"
  | UnaryOperator _ -> failwith "translate_expr: unary operator"

  | BinaryOperator {lhs; kind = Assign; rhs} ->
      let lhs = translate_expr env (Clang.Type.of_node lhs |> translate_typ) lhs in
      let rhs = translate_expr env (Clang.Type.of_node rhs |> translate_typ) rhs in
      begin match lhs.node with
      (* Special-case rewriting for buffer assignments *)
      | EBufRead (base, index) -> EBufWrite (base, index, rhs)
      | _ -> EAssign (lhs, rhs)
      end

  | BinaryOperator {lhs; kind; rhs} ->
      let lhs_ty = Clang.Type.of_node lhs |> translate_typ in
      let lhs = translate_expr env lhs_ty lhs in
      let rhs = translate_expr env (Clang.Type.of_node rhs |> translate_typ) rhs in
      let kind = translate_binop kind in
      (* TODO: Likely need a "assert_tint_or_tbool" *)
      let lhs_w = Helpers.assert_tint lhs_ty in
      let op_type = Helpers.type_of_op kind (Helpers.assert_tint lhs_ty) in
      let op : Ast.expr = with_type op_type (EOp (kind, lhs_w)) in
      EApp (op, [lhs; rhs])

  | DeclRef {name; _} -> get_id_name name |> find_var env
  | ArraySubscript {base; index} ->
      let base = translate_expr env (TBuf (t, false)) base in
      let index = translate_expr env (TInt SizeT) index in
      (* Is this only called on rvalues? Otherwise, might need EBufWrite *)
      EBufRead (base, index)

  | _ -> failwith "translate_expr"

and translate_expr (env: env) (t: typ) (e: expr) : Ast.expr =
  Ast.with_type t (translate_expr' env t e)

let translate_vardecl (env: env) (vdecl: var_decl_desc) : env * binder * Ast.expr =
  let name = vdecl.var_name in
  let typ = translate_typ vdecl.var_type in
  match vdecl.var_init with
  | None -> failwith "Variable declarations without definitions are not supported"
  | Some e -> add_var env name, Helpers.fresh_binder name typ, translate_expr env typ e

let rec translate_stmt' (env: env) (t: typ) (s: stmt_desc) : expr' = match s with
  | Compound l -> begin match l with
    | [] -> EUnit
    | hd :: tl -> match hd.desc with
      | Decl [{desc = Var vdecl; _ }] ->
          let env', b, e = translate_vardecl env vdecl in
          ELet (b, e, translate_stmt env' t (Compound tl))
      | Decl [_] -> failwith "This decl is not a var declaration"
      | Decl _ -> failwith "multiple decls"
      | stmt -> ELet (
        Helpers.sequence_binding (),
        translate_stmt env TUnit stmt,
        translate_stmt (add_var env "_") t (Compound tl))
   end
  | Decl _ -> failwith "translate_stmt: decl"
  | Expr e -> translate_expr' env t e
  | _ -> failwith "translate_stmt"

and translate_stmt (env: env) (t: typ) (s: stmt_desc) : Ast.expr =
  Ast.with_type t (translate_stmt' env t s)

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
  let body = match fdecl.body with
    | None -> Helpers.eunit
    | Some s -> translate_stmt env ret_type s.desc
  in
  let decl = Ast.(DFunction (None, [], 0, 0, ret_type, ([], name), args, body)) in
  KPrint.bprintf "Resulting decl %a\n" PrintAst.pdecl decl;
  decl


let translate_decl (decl: decl) = match decl.desc with
  | Function fdecl ->
    let name = get_id_name fdecl.name in
    Printf.printf "Translating function %s\n" name;
    if name = "test" || name = "quarter_round" then
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


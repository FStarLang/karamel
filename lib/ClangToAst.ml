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

(* TODO: Handle fully qualified names/namespaces/different files *)
let find_var env var =
  try EBound (KList.index (fun x -> x = var) env.vars) with
  (* This variable is not a local var *)
  | Not_found -> EQualified ([], var)

let get_id_name (dname: declaration_name) = match dname with
  | IdentifierName s -> s
  | ConstructorName _ -> failwith "constructor"
  | DestructorName _ -> failwith "destructor"
  | ConversionFunctionName _ -> failwith "conversion function"
  | DeductionGuideName _ -> failwith "deduction guide"
  | OperatorName _ -> failwith "operator name"
  | LiteralOperatorName _ -> failwith "literal operator name"
  | UsingDirectiveName -> failwith "using directive"

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
  | s ->
      Printf.printf "type name %s is unsupported\n" s;
      failwith "unsupported name"

let translate_builtin_typ (t: Clang__Clang__ast.builtin_type) = match t with
  | Void -> TUnit
  | UInt -> TInt UInt32 (* TODO: How to retrieve exact width? *)
  | Pointer -> failwith "translate_builtin_typ: pointer"
  | _ -> failwith "translate_builtin_typ: unsupported builtin type"

let rec translate_typ (typ: qual_type) = match typ.desc with
  | Pointer typ -> TBuf (translate_typ typ, false)

  | LValueReference _ -> failwith "translate_typ: lvalue reference"
  | RValueReference _ -> failwith "translate_typ: rvalue reference"
  | ConstantArray _ -> failwith "translate_typ: constant array"
  | Enum _ -> failwith "translate_typ: enum"

  | FunctionType {result; parameters; _} ->
      let ret_typ = translate_typ result in
      begin match parameters with
      | None -> TArrow (TUnit, ret_typ)
      | Some params ->
          (* Not handling variadic parameters *)
          assert (not (params.variadic));
          let ts = List.map
            (fun (p: parameter) -> translate_typ p.desc.qual_type)
            params.non_variadic
          in
          Helpers.fold_arrow ts ret_typ
      end

  | Record  _ -> failwith "translate_typ: record"


  | Typedef {name; _} -> get_id_name name |> translate_typ_name

  | BuiltinType t -> translate_builtin_typ t

  | _ -> failwith "translate_typ: unsupported type"

(* Takes a Clangml expression [e], and retrieves the corresponding karamel Ast type *)
let typ_of_expr (e: expr) : typ = Clang.Type.of_node e |> translate_typ

(* Translate expression [e], with expected type [t] *)
let rec translate_expr' (env: env) (t: typ) (e: expr) : expr' = match e.desc with
  | IntegerLiteral (Int n) -> EConstant (Helpers.assert_tint t, string_of_int n)

  | FloatingLiteral _ -> failwith "translate_expr: floating literal"
  | StringLiteral _ -> failwith "translate_expr: string literal"
  | CharacterLiteral _ -> failwith "translate_expr character literal"
  | ImaginaryLiteral _ -> failwith "translate_expr: imaginary literal"
  | BoolLiteral _ -> failwith "translate_expr: bool literal"
  | NullPtrLiteral -> failwith "translate_expr: null ptr literal"

  | UnaryOperator _ -> failwith "translate_expr: unary operator"

  | BinaryOperator {lhs; kind = Assign; rhs} ->
      let lhs = translate_expr env (typ_of_expr lhs) lhs in
      let rhs = translate_expr env (typ_of_expr rhs) rhs in
      begin match lhs.node with
      (* Special-case rewriting for buffer assignments *)
      | EBufRead (base, index) -> EBufWrite (base, index, rhs)
      | _ -> EAssign (lhs, rhs)
      end

  | BinaryOperator {lhs; kind; rhs} ->
      let lhs_ty = typ_of_expr lhs in
      let lhs = translate_expr env lhs_ty lhs in
      let rhs = translate_expr env (typ_of_expr rhs) rhs in
      let kind = translate_binop kind in
      (* TODO: Likely need a "assert_tint_or_tbool" *)
      let lhs_w = Helpers.assert_tint lhs_ty in
      let op_type = Helpers.type_of_op kind (Helpers.assert_tint lhs_ty) in
      let op : Ast.expr = with_type op_type (EOp (kind, lhs_w)) in
      EApp (op, [lhs; rhs])

  | DeclRef {name; _} -> get_id_name name |> find_var env

  | Call {callee; args} ->
      (* In C, a function type is a pointer. We need to strip it to retrieve
         the standard arrow abstraction *)
      let fun_typ = Helpers.assert_tbuf (typ_of_expr callee) in
      let callee = translate_expr env fun_typ callee in
      let args = List.map (fun x -> translate_expr env (typ_of_expr x) x) args in
      EApp (callee, args)

  | Cast _ -> failwith "translate_expr: cast"

  | ArraySubscript {base; index} ->
      let base = translate_expr env (TBuf (t, false)) base in
      let index = translate_expr env (TInt SizeT) index in
      (* Is this only called on rvalues? Otherwise, might need EBufWrite *)
      EBufRead (base, index)

  | ConditionalOperator _ -> failwith "translate_expr: conditional operator"

  | _ -> failwith "translate_expr: unsupported expression"

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
  (* KPrint.bprintf "Resulting decl %a\n" PrintAst.pdecl decl; *)
  decl


let builtins = [
  (* Functions from inttypes.h *)
  "imaxabs"; "imaxdiv"; "strtoimax"; "strtoumax"; "wcstoimax"; "wcstoumax"
]

let translate_decl (decl: decl) = match decl.desc with
  | Function fdecl ->
    let name = get_id_name fdecl.name in
    Printf.printf "Translating function %s\n" name;
    (* TODO: How to handle libc? *)
    if List.mem name builtins then None else Some (translate_fundecl fdecl)
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


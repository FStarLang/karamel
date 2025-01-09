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

(* TODO: Handle fully qualified names/namespaces/different files. *)
let find_var env var =
  try EBound (KList.index (fun x -> x = var) env.vars) with
  (* This variable is not a local var *)
  (* TODO: More robust check, likely need env for top-level decls *)
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

let is_assign_op (kind: Clang__Clang__ast.binary_operator_kind) = match kind with
  | Assign | AddAssign | MulAssign | DivAssign | RemAssign
  | SubAssign | ShlAssign | ShrAssign | AndAssign
  | XorAssign | OrAssign -> true
  | _ -> false

let assign_to_bop (kind: Clang__Clang__ast.binary_operator_kind) : Ast.expr =
  let op = match kind with
  (* TODO: Might need to disambiguate for pointer arithmetic *)
  | AddAssign -> K.Add
  | MulAssign -> Mult
  | DivAssign -> Div
  | RemAssign -> Mod
  | SubAssign -> Sub
  | ShlAssign -> BShiftL
  | ShrAssign -> BShiftR
  | AndAssign -> BAnd
  (* TODO: Disambiguate *)
  | XorAssign -> BXor
  | OrAssign -> BOr
  | _ -> failwith "not an assign op"
  in
  (* TODO: Infer width and type from types of operands *)
  Ast.with_type Helpers.uint32 (EOp (op, UInt32))

let translate_binop (kind: Clang__Clang__ast.binary_operator_kind) : K.op = match kind with
  | PtrMemD | PtrMemI -> failwith "translate_binop: ptr mem"
  | Mul | Div | Rem -> failwith " translate_binop: arith expr"

  (* TODO: Might need to disambiguate for pointer arithmetic *)
  | Add -> Add
  | Sub -> Sub

  | Shl -> BShiftL
  | Shr -> BShiftR

  | Cmp | LT | GT | LE | GE | EQ | NE -> failwith "translate_binop: boolcomp"

  | And -> BAnd
  (* TODO: How to distinguish between Xor and BXor? Likely need typing info from operands *)
  | Xor -> BXor
  | Or -> BOr

  | LAnd | LOr -> failwith "translate_binop: logical ops"

  | Assign | AddAssign | MulAssign | DivAssign | RemAssign
  | SubAssign | ShlAssign | ShrAssign | AndAssign
  | XorAssign | OrAssign ->
      failwith "Assign operators should have been previously rewritten"

  | Comma -> failwith "translate_binop: comma"
  | InvalidBinaryOperator -> failwith "translate_binop: invalid binop"

let translate_typ_name = function
  | "size_t" -> Helpers.usize
  | "uint32_t" -> Helpers.uint32
  | s ->
      Printf.printf "type name %s is unsupported\n" s;
      failwith "unsupported name"

let translate_builtin_typ (t: Clang__Clang__ast.builtin_type) = match t with
  | Void -> TUnit
  | UInt -> TInt UInt32 (* TODO: How to retrieve exact width? *)
  | UShort -> failwith "translate_builtin_typ: ushort"
  | ULong -> TInt UInt32
  | ULongLong -> failwith "translate_builtin_typ: ulonglong"
  | UInt128 -> failwith "translate_builtin_typ: uint128"

  | Int -> TInt Int32 (* TODO: Retrieve exact width *)

  | Short
  | Long
  | LongLong
  | Int128 -> failwith "translate_builtin_typ: signed int"

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

(* Check whether a given Clang expression is a memcpy callee *)
let is_memcpy (e: expr) = match e.desc with
  | DeclRef { name; _ } ->
      let name = get_id_name name in
      name = "__builtin___memcpy_chk"
  | _ -> false



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

  | BinaryOperator {lhs; kind; rhs} when is_assign_op kind ->
      let lhs_ty = typ_of_expr lhs in
      let lhs = translate_expr env (typ_of_expr lhs) lhs in
      let rhs = translate_expr env (typ_of_expr rhs) rhs in
      (* Rewrite the rhs into the compound expression, using the underlying operator *)
      let rhs = Ast.with_type lhs_ty (EApp (assign_to_bop kind, [lhs; rhs])) in
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

  | Call {callee; args} when is_memcpy callee ->
      (* Format.printf "Trying to translate memcpy %a@." Clang.Expr.pp e; *)
      begin match args with
      (* We are assuming here that this is __builtin___memcpy_chk.
         This function has a fourth argument, corresponding to the number of bytes
         remaining in dst. We omit it during the translation *)
      | [dst; src; len; _] ->
          let dst = translate_expr env (typ_of_expr dst) dst in
          let src = translate_expr env (typ_of_expr src) src in
          begin match len.desc with
          | BinaryOperator {lhs; kind = Mul; rhs = { desc = UnaryExpr {kind = SizeOf; _}; _}} ->
              let len = translate_expr env Helpers.usize lhs in
              EBufBlit (src, Helpers.zerou32, dst, Helpers.zerou32, len)
          | _ -> failwith "ill-formed memcpy"
          end
      | _ -> failwith "memcpy does not have the right number of arguments"
      end

  | Call {callee; args} ->
      (* In C, a function type is a pointer. We need to strip it to retrieve
         the standard arrow abstraction *)
      let fun_typ = Helpers.assert_tbuf (typ_of_expr callee) in
      (* Format.printf "Trying to translate function call %a@." Clang.Expr.pp callee; *)
      let callee = translate_expr env fun_typ callee in
      let args = List.map (fun x -> translate_expr env (typ_of_expr x) x) args in
      EApp (callee, args)

  | Cast {qual_type; operand; _} ->
      (* Format.printf "Cast %a@."  Clang.Expr.pp e; *)
      let typ = translate_typ qual_type in
      let e = translate_expr env (typ_of_expr operand) operand in
      ECast (e, typ)

  | ArraySubscript {base; index} ->
      let base = translate_expr env (TBuf (t, false)) base in
      let index = translate_expr env (TInt SizeT) index in
      (* Is this only called on rvalues? Otherwise, might need EBufWrite *)
      EBufRead (base, index)

  | ConditionalOperator _ -> failwith "translate_expr: conditional operator"
  | Paren _ -> failwith "translate_expr: paren"

  | _ ->
    Format.printf "Trying to translate expression %a@." Clang.Expr.pp e;
    failwith "translate_expr: unsupported expression"

and translate_expr (env: env) (t: typ) (e: expr) : Ast.expr =
  Ast.with_type t (translate_expr' env t e)

let translate_vardecl (env: env) (vdecl: var_decl_desc) : env * binder * Ast.expr =
  let name = vdecl.var_name in
  let typ = translate_typ vdecl.var_type in
  match vdecl.var_init with
  | None -> failwith "Variable declarations without definitions are not supported"
  | Some e -> add_var env name, Helpers.fresh_binder name typ, translate_expr env typ e

let rec translate_stmt' (env: env) (t: typ) (s: stmt_desc) : expr' = match s with
  | Null -> failwith "translate_stmt: null"

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

  | For  _ -> failwith "translate_stmt: for"
  | ForRange _ -> failwith "translate_stmt: for range"
  | If _ -> failwith "translate_stmt: if"

  | Switch _ -> failwith "translate_stmt: switch"
  | Case _ -> failwith "translate_stmt: case"
  | Default _ -> failwith "translate_stmt: default"

  | While _ -> failwith "translate_stmt: while"
  | Do { body; cond } ->
    (* The do statements first executes the body before behaving as a while loop.
       We thus translate it as a sequence of the body and the corresponding while loop *)
    let body = translate_stmt env t body.desc in
    (* TODO: Likely need to translate int conditions to boolean expressions *)
    let cond = translate_expr env (typ_of_expr cond) cond in
    ELet (
      Helpers.sequence_binding (),
      body,
      Ast.with_type TUnit (EWhile (cond, body))
    )

  | Label _ -> failwith "translate_stmt: label"
  | Goto _ -> failwith "translate_stmt: goto"
  | IndirectGoto _ -> failwith "translate_stmt: indirect goto"

  | Continue -> failwith "translate_stmt: continue"
  | Break -> failwith "translate_stmt: break"
  | Asm _ -> failwith "translate_stmt: asm"
  | Return _ -> failwith "translate_stmt: return"

  | Decl _ -> failwith "translate_stmt: decl"
  | Expr e -> translate_expr' env t e

  | Try _ -> failwith "translate_stmt: try"
  | AttributedStmt _ -> failwith "translate_stmt: AttributedStmt"
  | UnknownStmt _ -> failwith "translate_stmt: UnknownStmt"

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

(* TODO: Builtins might not be needed with a cleaner support for multiple files *)
let builtins = [
  (* Functions from inttypes.h *)
  "imaxabs"; "imaxdiv"; "strtoimax"; "strtoumax"; "wcstoimax"; "wcstoumax";
  (* From string.h *)
  "__sputc"; "_OSSwapInt16"; "_OSSwapInt32"; "_OSSwapInt64";
  (* Krml functions. TODO: Should be handled as multifile *)
  "krml_time";
]

(* Returning an option is only a hack to make progress.
   TODO: Proper handling of  decls *)
let translate_decl (decl: decl) = match decl.desc with
  | Function fdecl ->
    let name = get_id_name fdecl.name in
    (* TODO: How to handle libc? *)
    let loc = Clang.Ast.location_of_node decl |> Clang.Ast.concrete_of_source_location File in
    let file_loc = loc.filename in
    (* TODO: Support multiple files *)
    if file_loc = "test.c" then (
        Printf.printf "Translating function %s\n" name;
        Some (translate_fundecl fdecl)
    ) else None
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


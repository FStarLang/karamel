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

let translate_unop (kind: Clang__Clang__ast.unary_operator_kind) : K.op = match kind with
  | PostInc -> PostIncr
  | PostDec -> PostDecr
  | PreInc -> PreIncr
  | PreDec -> PreDecr
  | AddrOf -> failwith "translate_unop: addrof"
  | Deref -> failwith "translate_unop: deref"
  | Plus -> failwith "translate_unop: plus"
  | Minus -> failwith "translate_unop: minus"
  | Not -> failwith "translate_unop: not"
  | LNot -> failwith "translate_unop: lnot"
  | Real -> failwith "translate_unop: real"
  | Imag -> failwith "translate_unop: imag"
  | Extension -> failwith "translate_unop: extension"
  | Coawait -> failwith "translate_unop: coawait"
  | InvalidUnaryOperator -> failwith "translate_unop: invalid unop"

let translate_binop (kind: Clang__Clang__ast.binary_operator_kind) : K.op = match kind with
  | PtrMemD | PtrMemI -> failwith "translate_binop: ptr mem"

  (* Disambiguation for pointer arithmetic must be done when calling translate_binop:
     This is a deeper rewriting than just disambiguating between two K.op *)
  | Add -> Add
  | Sub -> Sub
  | Mul -> Mult

  | Div | Rem -> failwith " translate_binop: arith expr"

  | Shl -> BShiftL
  | Shr -> BShiftR

  | Cmp -> failwith "translate_binop: cmp"

  | LT -> Lt
  | GT -> Gt
  | LE -> Lte
  | GE -> Gte
  | EQ -> Eq
  | NE -> Neq

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
  | "uint8_t" -> Helpers.uint8
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

  | UnaryOperator {kind = PostInc; operand = { desc = DeclRef {name; _}; _ }} ->
      (* This is a special case for loop increments. The current Karamel
         extraction pipeline only supports a specific case of loops *)
      let var_name = get_id_name name in
      (* TODO: Retrieve correct width *)
      let w = K.UInt32 in
      let t = TInt w in
      let v = find_var env var_name in
      (* We rewrite `name++` into `name := name + 1` *)
      EAssign (
        Ast.with_type t v,
        Ast.with_type t (EApp (Helpers.mk_op K.Add w, [Ast.with_type t v; Helpers.one w]))
      )

  | UnaryOperator _ ->
      failwith "translate_expr: unary operator"

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
      (* In case of pointer arithmetic, we need to perform a rewriting into EBufSub/Diff *)
      begin match lhs_ty, kind with
      | TBuf _, Add -> EBufSub (lhs, rhs)
      | TBuf _, Sub -> EBufDiff (lhs, rhs)
      | _ ->
        (* TODO: Likely need a "assert_tint_or_tbool" *)
        let lhs_w = Helpers.assert_tint lhs_ty in
        let op_type = Helpers.type_of_op kind (Helpers.assert_tint lhs_ty) in
        let op : Ast.expr = with_type op_type (EOp (kind, lhs_w)) in
        EApp (op, [lhs; rhs])
      end

  | DeclRef {name; _} -> get_id_name name |> find_var env

  | Call {callee; args} when is_memcpy callee ->
      (* Format.printf "Trying to translate memcpy %a@." Clang.Expr.pp e; *)
      begin match args with
      (* We are assuming here that this is __builtin___memcpy_chk.
         This function has a fourth argument, corresponding to the number of bytes
         remaining in dst. We omit it during the translation *)
      | [dst; src; len; _] ->
          (* TODO: The type returned by clangml for the arguments is void*.
             Hardcoding it to TBuf uint32 to make progress, but to fix

             In particular, clang-analyzer is able to find the correct type.
             If we cannot get it through clangml, we could alternatively retrieve the type
             from the sizeof multiplication
          *)
          let dst = translate_expr env (TBuf (Helpers.uint32, false)) dst in
          let src = translate_expr env (TBuf (Helpers.uint32, false)) src in
          begin match len.desc with
          (* We recognize the case `len = lhs * sizeof (_)` *)
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

  | For {init; condition_variable; cond; inc; body} ->
      assert (condition_variable = None);
      begin match init, cond, inc with
      | Some init, Some cond, Some inc ->
          begin match init.desc with
          | Decl [{desc = Var vdecl; _}] ->
            let env, b, init = translate_vardecl env vdecl in
            let cond = translate_expr env (typ_of_expr cond) cond in
            let inc = translate_stmt env TUnit inc.desc in
            let body = translate_stmt env t body.desc in
            EFor (b, init, cond, inc, body)
          | _ -> failwith "loop variable must be declared in for loop initializer"
          end
      | _ -> failwith "translation of for loops requires initialize, condition, and increment"
      end

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
    let cond_ty = typ_of_expr cond in
    let cond = translate_expr env cond_ty cond in
    let cond = match cond_ty with
      | TBool -> cond
      | TInt w ->
        (* If we have an integer expression [e], the condition is equivalent to `e != 0` *)
        Helpers.mk_neq cond (Helpers.zero w)
      | _ -> failwith "incorrect type for while condition"
    in
    ESequence [
      body;
      Ast.with_type TUnit (EWhile (cond, body))
    ]

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

(* Returning an option is only a hack to make progress.
   TODO: Proper handling of  decls *)
let translate_decl (decl: decl) = match decl.desc with
  | Function fdecl ->
    (* TODO: How to handle libc? *)
    let loc = Clang.Ast.location_of_node decl |> Clang.Ast.concrete_of_source_location File in
    let file_loc = loc.filename in
    (* TODO: Support multiple files *)
    if file_loc = "test.c" then (
        (* let name = get_id_name fdecl.name in
           Printf.printf "Translating function %s\n" name; *)
        Some (translate_fundecl fdecl)
    ) else None
  | _ -> None

let read_file () =
  let command_line_args = ["-DKRML_UNROLL_MAX 0"] in
  let ast = parse_file ~command_line_args "test.c" in
  (* Format.printf "@[%a@]@." (Refl.pp [%refl: Clang.Ast.translation_unit] []) ast; *)
  (* Printf.printf "Trying file %s\n" ast.desc.filename; *)
  let decls = List.filter_map translate_decl ast.desc.items in
  let files = ["test", decls] in
  let files = Simplify.sequence_to_let#visit_files () files in
  let files = AstToMiniRust.translate_files files in
  let files = OptimizeMiniRust.cleanup_minirust files in
  let files = OptimizeMiniRust.infer_mut_borrows files in
  let files = OptimizeMiniRust.simplify_minirust files in
  OutputRust.write_all files


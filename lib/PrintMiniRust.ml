(* We go directly from MiniRust to a rendering. Mostly, on the basis that
   MiniRust is close to actual Rust that we can print out syntax on the fly
   (unlike C, where for instance the types are so different that we need to have
   a different AST before going to print). *)

open PPrint
open PrintCommon
open MiniRust

let is_block_expression e =
  match e with
  | IfThenElse _ | For _ | While _ -> true
  | _ -> false

type env = {
  vars: [ `Named of string | `GoneUnit ] list;
  prefix: string list;
}
let push env x = { env with vars = x :: env.vars }
let lookup env x = List.nth env.vars x
let fresh prefix = { vars = []; prefix }
let print env =
  print_endline (String.concat ", " (List.map (function
    | `Named x -> x
    | `GoneUnit -> "–"
  ) env.vars))

let string_of_width (w: Constant.width) =
  match w with
  | Constant.UInt8 -> "u8"
  | Constant.UInt16 -> "u16"
  | Constant.UInt32 -> "u32"
  | Constant.UInt64 -> "u64"
  | Constant.Int8 -> "i8"
  | Constant.Int16 -> "i16"
  | Constant.Int32 -> "i32"
  | Constant.Int64 -> "i64"
  | Constant.Bool -> "bool"
  | Constant.SizeT -> "usize"
  | Constant.CInt -> failwith "unexpected: cint"
  | Constant.PtrdiffT -> failwith "unexpected: ptrdifft"

let print_borrow_kind k =
  match k with
  | Mut -> string "mut" ^^ break1
  | Shared -> empty

let print_constant (w, s) =
  string s ^^ string (string_of_width w)

let rec print_typ (t: typ): document =
  match t with
  | Constant w -> string (string_of_width w)
  | Ref (k, t) -> group (ampersand ^^ print_borrow_kind k ^^ print_typ t)
  | Vec t -> group (string "Vec" ^^ angles (print_typ t))
  | Array (t, n) -> group (brackets (print_typ t ^^ semi ^/^ int n))
  | Slice t -> group (brackets (print_typ t))
  | Unit -> parens empty
  | Function (ts, t) ->
      group @@
      group (parens (separate_map (comma ^^ break1) print_typ ts)) ^/^
      print_typ t

let print_binding (x, t) =
  string x ^^ colon ^/^ print_typ t

let rec print_block env (e: expr): document =
  if is_block_expression e then
    print_expr env max_int e
  else
    braces_with_nesting (print_statements env e)

and print_statements env (e: expr): document =
  match e with
  | Let ((_, Unit), e1, e2) ->
      print_expr env max_int e1 ^^ semi ^^ hardline ^^
      print_statements (push env (`GoneUnit)) e2
  | Let ((x, _) as b, e1, e2) ->
      group (
        group (string "let" ^/^ print_binding b ^/^ equals) ^^
        nest 2 (break 1 ^^ print_expr env max_int e1) ^^ semi) ^^ hardline ^^
      print_statements (push env (`Named x)) e2
  | _ ->
      print_expr env max_int e

(*

The precedence of Rust operators and expressions is ordered as follows, going
from strong to weak. Binary Operators at the same precedence level are grouped
in the order given by their associativity.

Level	Operator/Expression		Associativity
=====	===================		=============
 1	Paths
 2	Method calls
 3	Field expression		left to right
 4	Function calls, array indexing
 5	?
 6	Unary - * ! & &mut
 7	as				left to right
 8	* / %				left to right
 9	+				left to right
10	<< >>				left to right
11	&				left to right
12	^				left to right
13	|				left to right
14	== != < > <= >=			Require parentheses
15	&&				left to right
16	||				left to right
17	.. ..=				Require parentheses
18	= += -= *= /= %=
  	&= |= ^= <<= >>=		right to left
19	return break closures

*)

(* See PrintC for the original inspiration. We return <ours>, <left>, <right> *)
and prec_of_op2 o =
  let open Constant in
  match o with
  | Mult | Div | Mod -> 8, 8, 7
  | Add -> 9, 9, 8
  | BShiftL | BShiftR -> 10, 10, 9
  | BAnd -> 11, 11, 10
  | BXor -> 12, 12, 11
  | BOr -> 13, 13, 12
  | Eq | Neq | Lt | Gt | Lte | Gte -> 0, 13, 13
  | And -> 15, 15, 14
  | Or -> 16, 16, 15
  | _ -> failwith ("unexpected: unknown binary operator: " ^ Constant.show_op o)

and prec_of_op1 o =
  let open Constant in
  match o with
  | Not | BNot | Neg -> 6
  | _ -> failwith "unexpected: unknown unary operator"


and print_name env n =
  let n =
    if List.length n > List.length env.prefix && fst (KList.split (List.length env.prefix) n) = env.prefix then
      snd (KList.split (List.length env.prefix) n)
    else
      n
  in
  group (separate_map (colon ^^ colon) string n)

and print_expr env (context: int) (e: expr): document =
  (* If the current expressions precedence level exceeds that of the context, it
     needs to be parenthesized, otherwise it'll parse incorrectly. *)
  let paren_if mine doc =
    if mine > context then
      parens doc
    else
      doc
  in
  match e with
  | Operator _ ->
      failwith "unexpected: standalone operator"
  | Array e ->
      print_array_expr env e
  | VecNew e ->
      group (string "vec!" ^^ print_array_expr env e)
  | Name n ->
      print_name env n
  | Borrow (k, e) ->
      let mine = 6 in
      paren_if mine @@
      group (ampersand ^^ print_borrow_kind k ^/^ print_expr env mine e)
  | Constant c ->
      print_constant c
  | Let _ ->
      print_block env e
  | Call (Operator o, [ e1; e2 ]) ->
      let mine, left, right = prec_of_op2 o in
      paren_if mine @@
      group (print_expr env left e1 ^/^
        (nest 2 (print_op o) ^/^ print_expr env right e2))
  | Call (Operator o, [ e1 ]) ->
      let mine = prec_of_op1 o in
      paren_if mine @@
      group (print_op o ^/^ print_expr env mine e1)
  | Call (e, es) ->
      let mine = 4 in
      paren_if mine @@
      group (print_expr env mine e ^^ parens_with_nesting (
        separate_map (comma ^^ break1) (print_expr env max_int) es))
  | Unit ->
      lparen ^^ rparen
  | Panic msg ->
      group (string "panic!" ^^ parens_with_nesting (string msg))
  | IfThenElse (e1, e2, e3) ->
      group @@
      string "if" ^/^ print_expr env max_int e1 ^/^
      braces_with_nesting (print_block env e2) ^^
      begin match e3 with
      | Some e3 ->
          break1 ^^ string "else" ^/^ braces_with_nesting (print_block env e3)
      | None ->
          empty
      end
  | Assign (e1, e2) ->
      let mine, left, right = 18, 17, 18 in
      paren_if mine @@
      group (print_place env left e1 ^^ equals ^^
        (nest 2 (break1 ^^ print_expr env right e2)))
  | As (e1, e2) ->
      let mine = 7 in
      paren_if mine @@
      group (print_expr env mine e1 ^/^ string "as" ^/^ print_typ e2)
  | Place p ->
      print_place env context p
  | For (b, e1, e2) ->
      let env = push env (`Named (fst b)) in
      group @@
      group (string "for" ^/^ print_binding b ^/^ string "in" ^/^ print_expr env max_int e1) ^/^
      print_block env e2
  | While (e1, e2) ->
      group @@
      string "while" ^/^ print_expr env max_int e1 ^/^
      print_block env e2
  | MethodCall (e, path, es) ->
      let mine = 2 in
      paren_if mine @@
      group (print_expr env mine e ^^ dot ^^ print_name env path ^^ parens_with_nesting (
        separate_map (comma ^^ break1) (print_expr env max_int) es))
  | Range (e1, e2, inclusive) ->
      let mine = 17 in
      let module Option = Stdlib.Option in
      paren_if mine @@
      let e1 = Option.value ~default:empty (Option.map (print_expr env mine) e1) in
      let e2 = Option.value ~default:empty (Option.map (print_expr env mine) e2) in
      let inclusive = if inclusive then equals else empty in
      e1 ^^ dot ^^ dot ^^ e2 ^^ inclusive

and print_place env context p =
  let paren_if mine doc =
    if mine > context then
      parens doc
    else
      doc
  in
  match p with
  | Var v ->
      begin match lookup env v with
      | `Named x -> string x
      | `GoneUnit -> print env; failwith "unexpected: unit-returning computation was let-bound and used"
      end
  | Index (p, e) ->
      let mine = 4 in
      paren_if mine @@
      print_expr env mine p ^^ group (brackets (print_expr env max_int e))

and print_array_expr env (e: array_expr) =
  match e with
  | List es ->
      group @@
      brackets (nest 2 (separate_map (comma ^^ break1) (print_expr env max_int) es))
  | Repeat (e, n) ->
      group @@
      print_expr env max_int e ^^ semi ^/^ print_expr env max_int n

let arrow = string "->"

let print_decl ns (d: decl) =
  let env = fresh ns in
  match d with
  | Function { name; parameters; return_type; body } ->
      let env = List.fold_left (fun env (x, _) -> push env (`Named x)) env parameters in
      group @@
      group (group (string "fn" ^/^ print_name env name) ^^
        parens_with_nesting (separate_map (comma ^^ break1) print_binding parameters) ^^
        space ^^ arrow ^^ (nest 2 (break1 ^^ print_typ return_type))) ^/^
      print_block env body
  | Constant { name; typ; body } ->
      group @@
      group (string "const" ^/^ print_name env name ^^ colon ^/^ print_typ typ ^/^ equals) ^^
      nest 2 (break1 ^^ print_expr env max_int body)

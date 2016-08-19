(** Pretty-printer that conforms with C syntax. Also defines the grammar of
 * concrete C syntax, as opposed to our idealistic, well-formed C*. *)

open PPrint
open PrintCommon
open C

(* Pretty-printing of actual C syntax *****************************************)

let c99_macro_for_width w =
  let open Constant in
  match w with
  | UInt8  -> Some "UINT8_C"
  | UInt16 -> Some "UINT16_C"
  | UInt32 -> Some "UINT32_C"
  | UInt64 -> Some "UINT64_C"
  | Int8   -> Some "INT8_C"
  | Int16  -> Some "INT16_C"
  | Int32  -> Some "INT32_C"
  | Int64  -> Some "INT64_C"
  | Bool -> None

let p_constant (w, s) =
  match c99_macro_for_width w with
  | Some m ->
      string m ^^ lparen ^^ string s ^^ rparen
  | None ->
      string s

let p_storage_spec = function
  | Typedef -> string "typedef"

let rec p_type_spec = function
  | Int w -> print_width w ^^ string "_t"
  | Void -> string "void"
  | Named s -> string s
  | Struct (name, decls) ->
      string "struct" ^/^
      (match name with Some name -> string name ^^ break1 | None -> empty) ^^
      braces_with_nesting (separate_map break1 (fun p -> group (p_declaration p ^^ semi)) decls)

and p_type_declarator d =
  let rec p_noptr = function
    | Ident n ->
        string n
    | Array (d, s) ->
        p_noptr d ^^ lbracket ^^ p_expr s ^^ rbracket
    | Function (d, params) ->
        p_noptr d ^^ parens_with_nesting (separate_map (comma ^^ break 1) (fun (spec, decl) ->
          group (p_type_spec spec ^/^ p_any decl)
        ) params)
    | d ->
        lparen ^^ p_any d ^^ rparen
  and p_any = function
    | Pointer d ->
        star ^^ p_any d
    | d ->
        p_noptr d
  in
  p_any d

and p_type_name (spec, decl) =
  p_type_spec spec ^^ space ^^ p_type_declarator decl

(* http:/ /en.cppreference.com/w/c/language/operator_precedence *)
and prec_of_op2 op =
  let open Constant in
  match op with
  | AddW | SubW -> failwith "[prec_of_op]: should've been desugared"
  | Add -> 4, 4, 4
  | Sub -> 4, 4, 3
  | Div -> 3, 3, 2
  | Mult -> 3, 3, 3
  | Mod -> 3, 3, 2
  | BOr -> 10, 10, 10
  | BAnd -> 8, 8, 8
  | BXor | Xor -> 9, 9, 9
  | BShiftL -> 5, 5, 4
  | BShiftR -> 5, 5, 4
  | Eq | Neq -> 7, 7, 7
  | Lt | Lte | Gt | Gte -> 6, 6, 5
  | And -> 11, 11, 11
  | Or -> 12, 12, 12
  | Not -> raise (Invalid_argument "prec_of_op2")

and prec_of_op1 op =
  let open Constant in
  match op with
  | Not -> 2
  | _ -> raise (Invalid_argument "prec_of_op1")

(* The precedence level [curr] is the maximum precedence the current node should
 * have. If it doesn't, then it should be parenthesized. Lower numbers bind
 * tighter. *)
and paren_if curr mine doc =
  if curr < mine then
    group (lparen ^^ doc ^^ rparen)
  else
    doc

and p_expr' curr = function
  | Op1 (op, e1) ->
      let mine = prec_of_op1 op in
      let e1 = p_expr' mine e1 in
      paren_if curr mine (print_op op ^^ e1)
  | Op2 (op, e1, e2) ->
      let mine, left, right = prec_of_op2 op in
      let e1 = p_expr' left e1 in
      let e2 = p_expr' right e2 in
      paren_if curr mine (e1 ^/^ print_op op ^^ jump e2)
  | Index (e1, e2) ->
      let mine, left, right = 1, 1, 15 in
      let e1 = p_expr' left e1 in
      let e2 = p_expr' right e2 in
      paren_if curr mine (e1 ^^ lbracket ^^ e2 ^^ rbracket)
  | Assign (e1, e2) ->
      let mine, left, right = 14, 13, 14 in
      let e1 = p_expr' left e1 in
      let e2 = p_expr' right e2 in
      paren_if curr mine (group (e1 ^/^ equals) ^^ jump e2)
  | Call (e, es) ->
      let mine, left, arg = 1, 1, 15 in
      let e = p_expr' left e in
      let es = nest 2 (separate_map (comma ^^ break 1) (fun e -> group (p_expr' arg e)) es) in
      paren_if curr mine (e ^^ lparen ^^ es ^^ rparen)
  | Name s ->
      string s
  | Cast (t, e) ->
      let mine, right = 2, 2 in
      let e = group (p_expr' right e) in
      let t = p_type_name t in
      paren_if curr mine (lparen ^^ t ^^ rparen ^^ e)
  | Constant c ->
      p_constant c
  | Sizeof e ->
      let mine, right = 2, 2 in
      let e = p_expr' right e in
      paren_if curr mine (string "sizeof" ^^ space ^^ e)
  | Deref _ | Address _ | Member _ | MemberP _ ->
      failwith "[p_expr']: not implemented"
  | Bool b ->
      string (string_of_bool b)
  | CompoundLiteral (t, init) ->
      lparen ^^ p_type_name t ^^ rparen ^^
      braces_with_nesting (separate_map (comma ^^ break1) p_init init)
  | MemberAccess (expr, member) ->
      p_expr' 1 expr ^^ dot ^^ string member

and p_expr e = p_expr' 15 e

and p_init' l (i: init) =
  match i with
  | Designated (designator, expr) ->
      group (p_designator designator ^/^ equals ^/^ p_expr' l expr)
  | Expr e ->
      p_expr e
  | Initializer inits ->
      braces_with_nesting (separate_map (comma ^^ break 1) p_init inits)

and p_init i = p_init' 15 i

and p_designator = function
  | Dot ident ->
      dot ^^ string ident
  | Bracket i ->
      lbracket ^^ int i ^^ rbracket

and p_decl_and_init (decl, init) =
  group (p_type_declarator decl ^^ match init with
    | Some init ->
        space ^^ equals ^^ jump (p_init init)
    | None ->
        empty)

and p_declaration (spec, stor, decl_and_inits) =
  let stor = match stor with Some stor -> p_storage_spec stor ^^ break 1 | None -> empty in
  stor ^^ group (p_type_spec spec) ^^ space ^^
  separate_map (comma ^^ break 1) p_decl_and_init decl_and_inits

(* This is abusing the definition of a compound statement to ensure it is printed with braces. *)
let nest_if f stmt =
  match stmt with
  | Compound _ ->
      hardline ^^ f stmt
  | _ ->
      nest 2 (hardline ^^ f stmt)

let protect_solo_if s =
  match s with
  | SelectIf _ -> Compound [ s ]
  | _ -> s

let rec p_stmt (s: stmt) =
  (* [p_stmt] is responsible for appending [semi] and calling [group]! *)
  match s with
  | Compound stmts ->
      lbrace ^^ nest 2 (hardline ^^ separate_map hardline p_stmt stmts) ^^
      hardline ^^ rbrace
  | Expr expr ->
      group (p_expr expr ^^ semi)
  | SelectIf (e, stmt) ->
      group (string "if" ^/^ lparen ^^ p_expr e ^^ rparen) ^^
      nest_if p_stmt stmt
  | SelectIfElse (e, s1, s2) ->
      group (string "if" ^/^ lparen ^^ p_expr e ^^ rparen) ^^
      nest_if p_stmt (protect_solo_if s1) ^^ hardline ^^
      string "else" ^^
      (match s2 with
      | SelectIf _ | SelectIfElse _ ->
          space ^^ p_stmt s2
      | _ ->
        nest_if p_stmt s2)
  | Return None ->
      group (string "return" ^^ semi)
  | Return (Some e) ->
      group (string "return" ^/^ p_expr e ^^ semi)
  | Decl d ->
      group (p_declaration d ^^ semi)


let p_decl_or_function (df: declaration_or_function) =
  match df with
  | Decl d ->
      group (p_declaration d ^^ semi)
  | Function (d, stmt) ->
      group (p_declaration d) ^/^ p_stmt stmt

let print_files =
  PrintCommon.print_files p_decl_or_function

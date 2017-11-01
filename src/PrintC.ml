(** Pretty-printer that conforms with C syntax. Also defines the grammar of
 * concrete C syntax, as opposed to our idealistic, well-formed C*. *)

open PPrint
open PrintCommon
open C

(* Pretty-printing of actual C syntax *****************************************)

let p_storage_spec = function
  | Typedef -> string "typedef"
  | Extern -> string "extern"
  | Static -> string "static"

let rec p_type_spec = function
  | Int w -> print_width w ^^ string "_t"
  | Void -> string "void"
  | Named s -> string s
  | Union (name, decls) ->
      group (string "union" ^/^
      (match name with Some name -> string name ^^ break1 | None -> empty)) ^^
      braces_with_nesting (separate_map hardline (fun p -> group (p_declaration p ^^ semi)) decls)
  | Struct (name, decls) ->
      group (string "struct" ^/^
      (match name with Some name -> string name | None -> empty)) ^^
      (match decls with
      | Some decls ->
          break1 ^^ braces_with_nesting (separate_map hardline (fun p -> group (p_declaration p ^^ semi)) decls)
      | None ->
          empty)
  | Enum (name, tags) ->
      group (string "enum" ^/^
      (match name with Some name -> string name ^^ break1 | None -> empty)) ^^
      braces_with_nesting (separate_map (comma ^^ break1) string tags)


and p_type_declarator d =
  let rec p_noptr = function
    | Ident n ->
        string n
    | Array (d, s) ->
        p_noptr d ^^ lbracket ^^ p_expr s ^^ rbracket
    | Function (cc, d, params) ->
        let cc = match cc with Some cc -> print_cc cc ^^ break1 | None -> empty in
        group (cc ^^ p_noptr d ^^ parens_with_nesting (separate_map (comma ^^ break 1) (fun (spec, decl) ->
          group (p_type_spec spec ^/^ p_any decl)
        ) params))
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
  match decl with
  | Ident "" ->
      p_type_spec spec
  | _ ->
      p_type_spec spec ^^ space ^^ p_type_declarator decl

(* http:/ /en.cppreference.com/w/c/language/operator_precedence *)
and prec_of_op2 op =
  let open Constant in
  match op with
  | AddW | SubW | MultW | DivW -> failwith "[prec_of_op]: should've been desugared"
  | Add -> 4, 4, 4
  | Sub -> 4, 4, 3
  | Div -> 3, 3, 2
  | Mult -> 3, 3, 3
  | Mod -> 3, 3, 2
  | BOr -> 10, 10, 10
  | BAnd ->
      8, 8, 8
  | BXor | Xor -> 9, 9, 9
  | BShiftL | BShiftR ->
      5, 5, 4
  | Eq | Neq -> 7, 7, 7
  | Lt | Lte | Gt | Gte -> 6, 6, 5
  | And -> 11, 11, 11
  | Or -> 12, 12, 12
  | Assign -> 14, 13, 14
  | Comma -> 15, 15, 14
  | PreIncr | PostIncr | PreDecr | PostDecr | Not | BNot -> raise (Invalid_argument "prec_of_op2")

and prec_of_op1 op =
  let open Constant in
  match op with
  | PreDecr | PreIncr | Not | BNot -> 2
  | PostDecr | PostIncr -> 1
  | _ -> raise (Invalid_argument "prec_of_op1")

and is_prefix op =
  let open Constant in
  match op with
  | PreDecr | PreIncr | Not | BNot -> true
  | PostDecr | PostIncr -> false
  | _ -> raise (Invalid_argument "is_prefix")

(* The precedence level [curr] is the maximum precedence the current node should
 * have. If it doesn't, then it should be parenthesized. Lower numbers bind
 * tighter. *)
and paren_if curr mine doc =
  if curr < mine then
    group (lparen ^^ doc ^^ rparen)
  else
    doc

(* [e] is an operand of [op]; is this likely to trigger GCC's -Wparentheses? If
 * so, downgrade the current precedence to 0 to force parenthses. *)
and defeat_Wparentheses op e prec =
  let open Constant in
  if not !Options.parentheses then
    prec
  else match op, e with
  | (BShiftL | BShiftR | BXor | BOr | BAnd), Op2 ((Add | Sub | BOr | BXor), _, _) ->
      0
  | _ ->
      prec

and p_expr' curr = function
  | Op1 (op, e1) ->
      let mine = prec_of_op1 op in
      let e1 = p_expr' mine e1 in
      paren_if curr mine (if is_prefix op then print_op op ^^ e1 else e1 ^^ print_op op)
  | Op2 (op, e1, e2) ->
      let mine, left, right = prec_of_op2 op in
      let left = defeat_Wparentheses op e1 left in
      let right = defeat_Wparentheses op e2 right in
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
      let mine, left, arg = 1, 1, 14 in
      let e = p_expr' left e in
      let es = nest 2 (separate_map (comma ^^ break 1) (fun e -> group (p_expr' arg e)) es) in
      paren_if curr mine (e ^^ lparen ^^ es ^^ rparen)
  | Literal s ->
      dquote ^^ string s ^^ dquote
  | Constant (w, s) ->
      string s ^^ if K.is_unsigned w then string "U" else empty
  | Name s ->
      string s
  | Cast (t, e) ->
      let mine, right = 2, 2 in
      let e = group (p_expr' right e) in
      let t = p_type_name t in
      paren_if curr mine (lparen ^^ t ^^ rparen ^^ e)
  | Type t ->
      p_type_name t
  | Sizeof e ->
      let mine, right = 2, 2 in
      let e = p_expr' right e in
      paren_if curr mine (string "sizeof" ^^ space ^^ e)
  | Address e ->
      let mine, right = 2, 2 in
      let e = p_expr' right e in
      paren_if curr mine (ampersand ^^ e)
  | Deref e ->
      let mine, right = 2, 2 in
      let e = p_expr' right e in
      paren_if curr mine (star ^^ e)
  | Member _ | MemberP _ ->
      failwith "[p_expr']: not implemented"
  | Bool b ->
      string (string_of_bool b)
  | CompoundLiteral (t, init) ->
      (* NOTE: always parenthesize compound literal no matter what, because GCC
       * parses an application of a function to a compound literal as an n-ary
       * application. *)
      parens_with_nesting (
        lparen ^^ p_type_name t ^^ rparen ^^
        braces_with_nesting (separate_map (comma ^^ break1) p_init init)
      )
  | MemberAccess (expr, member) ->
      p_expr' 1 expr ^^ dot ^^ string member
  | MemberAccessPointer (expr, member) ->
      p_expr' 1 expr ^^ string "->" ^^ string member
  | InlineComment (s, e, s') ->
      surround 2 1 (p_comment s) (p_expr' curr e) (p_comment s')

and p_comment s =
  (* TODO: escape *)
  string "/* " ^^ nest 2 (flow space (words s)) ^^ string " */"


and p_expr e = p_expr' 15 e

and p_init (i: init) =
  match i with
  | Designated (designator, i) ->
      group (p_designator designator ^^ space ^^ equals ^^ space ^^ p_init i)
  | InitExpr e ->
      p_expr' 14 e
  | Initializer inits ->
      let inits =
        if List.length inits > 4 then
          flow (comma ^^ break1) (List.map p_init inits)
        else
          separate_map (comma ^^ break1) p_init inits
      in
      braces_with_nesting inits

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
  let stor = match stor with Some stor -> p_storage_spec stor ^^ space | None -> empty in
  stor ^^ group (p_type_spec spec) ^/^
  separate_map (comma ^^ break 1) p_decl_and_init decl_and_inits

(* This is abusing the definition of a compound statement to ensure it is printed with braces. *)
let nest_if f stmt =
  match stmt with
  | Compound _ ->
      hardline ^^ f stmt
  | _ ->
      nest 2 (hardline ^^ f stmt)

(* A note on the classic dangling else problem. Remember that this is how things
 * are parsed (note the indentation):
 *
 * if (foo)
 *   if (bar)
 *     ...
 *   else
 *     ...
 *
 * And remember that this needs braces:
 *
 * if (foo) {
 *   if (bar)
 *     ...
 * } else
 *   ...
 *
 * [protect_solo_if] adds braces to the latter case. However, GCC, unless
 * -Wnoparentheses is given, will produce a warning for the former case.
 * [protect_ite_if_needed] adds braces to the former case, when the user has
 * requested the extra, unnecessary parentheses needed to silence -Wparentheses.
 * *)
let protect_solo_if s =
  match s with
  | If _ -> Compound [ s ]
  | _ -> s

let protect_ite_if_needed s =
  match s with
  | IfElse _ when !Options.parentheses -> Compound [ s ]
  | _ -> s

let p_or p x =
  match x with
  | Some x -> p x
  | None -> empty

let rec p_stmt (s: stmt) =
  (* [p_stmt] is responsible for appending [semi] and calling [group]! *)
  match s with
  | Compound stmts ->
      lbrace ^^ nest 2 (hardline ^^ separate_map hardline p_stmt stmts) ^^
      hardline ^^ rbrace
  | Expr expr ->
      group (p_expr expr ^^ semi)
  | Comment s ->
      group (string "/*" ^/^ separate break1 (words s) ^/^ string "*/")
  | For (decl, e2, e3, stmt) ->
      let init = match decl with
        | `Decl decl -> p_declaration decl
        | `Expr expr -> p_expr expr
        | `Skip -> empty
      in
      group (string "for" ^/^ lparen ^^ nest 2 (
        init ^^ semi ^^ break1 ^^
        p_expr e2 ^^ semi ^^ break1 ^^
        p_expr e3
      ) ^^ rparen) ^^ nest_if p_stmt stmt
  | If (e, stmt) ->
      group (string "if" ^/^ lparen ^^ p_expr e ^^ rparen) ^^
      nest_if p_stmt (protect_ite_if_needed stmt)
  | IfElse (e, s1, s2) ->
      group (string "if" ^/^ lparen ^^ p_expr e ^^ rparen) ^^
      nest_if p_stmt (protect_solo_if s1) ^^ hardline ^^
      string "else" ^^
      (match s2 with
      | If _ | IfElse _ ->
          space ^^ p_stmt s2
      | _ ->
        nest_if p_stmt s2)
  | While (e, s) ->
      group (string "while" ^/^ lparen ^^ p_expr e ^^ rparen) ^^
      nest_if p_stmt s
  | Return None ->
      group (string "return" ^^ semi)
  | Return (Some e) ->
      group (string "return" ^^ jump (p_expr e ^^ semi))
  | Decl d ->
      group (p_declaration d ^^ semi)
  | Switch (e, branches, default) ->
      group (string "switch" ^/^ lparen ^^ p_expr e ^^ rparen) ^/^
      braces_with_nesting (
        separate_map hardline (fun (e, s) ->
          group (string "case" ^/^ p_expr e ^^ colon) ^^ nest 2 (
           hardline ^^ p_stmt s
          )
        ) branches ^^ hardline ^^
          string "default:" ^^ nest 2 (
           hardline ^^ p_stmt default
          )
      )
  | Break ->
     string "break" ^^ semi

let p_comments cs =
  separate_map hardline (fun c -> string ("/*\n" ^ c ^ "\n*/")) cs ^^
  if List.length cs > 0 then hardline else empty

let p_decl_or_function (df: declaration_or_function) =
  match df with
  | Decl (comments, d) ->
      p_comments comments ^^
      group (p_declaration d ^^ semi)
  | Function (comments, inline, d, stmt) ->
      p_comments comments ^^
      let inline = if inline then string "inline" ^^ space else empty in
      inline ^^ group (p_declaration d) ^/^ p_stmt stmt

let print_files =
  PrintCommon.print_files p_decl_or_function

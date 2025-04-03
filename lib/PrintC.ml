(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 and MIT Licenses. *)

(** Pretty-printer that conforms with C syntax. Also defines the grammar of
 * concrete C syntax, as opposed to our idealistic, well-formed C*. *)

module C = C11

open PPrint
open PrintCommon
open C

(* Pretty-printing of actual C syntax *****************************************)

let p_storage_spec = function
  | Typedef -> string "typedef"
  | Extern -> string "extern"
  | Static -> string "static"

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

let rec p_type_spec = function
  | Int w -> print_width w
  | Void -> string "void"
  | Named s -> string s
  | Union (name, decls) ->
      group (string "union" ^/^
      (match name with Some name -> string name ^^ break1 | None -> empty)) ^^
      (match decls with
      | Some decls ->
          braces_with_nesting (separate_map hardline (fun p -> group (p_declaration p ^^ semi)) decls)
      | None ->
          empty)
  | Struct (name, decls) ->
      (* If this is a tagged union, we name the union U, then generate the fancy constructor
         using a macro *)
      let decls, extra =
        match decls with
        | Some [ _, _, _, _, _, [ Ident "tag", _, _ ] as tag_decl;
            qs, Union (_, cases), is, ss, ex, ([ Ident "val", _, _ ] as val_decl) ] when
          !Options.cxx17_compat ->
            Some [ tag_decl; qs, Union (Some "U", cases), is, ss, ex, val_decl ],
            hardline ^^ string "KRML_UNION_CONSTRUCTOR" ^^ parens (string (Option.get name))
        | _ ->
            decls, empty
      in
      group (string "struct" ^/^
      (match name with Some name -> string name | None -> empty)) ^^
      (match decls with
      | Some decls ->
          break1 ^^ braces_with_nesting (separate_map hardline (fun p -> group (p_declaration p ^^
          semi)) decls ^^ extra)
      | None ->
          empty)
  | Enum (name, tags) ->
      group (string "enum" ^/^
      (match name with Some name -> string name ^^ break1 | None -> empty)) ^^
      braces_with_nesting (separate_map (comma ^^ break1) (fun (id, v) ->
        let suffix =
          match v with
          | Some v ->
              (* Some notes. 1) Must Z.of_string in the unlikely event that krml is running on a
                 32-bit machine. 2) This assert may be tripped as there is currently no code to
                 automatically decline -fenum for constants that don't fit. 3)  *)
              if not Z.(leq v (of_string "0xffffffff") && gt v (of_string "-0xffffffff")) then
                failwith ("Cannot use C11 enum for " ^ Option.value ~default:"???" name  ^ " since the value of one of the constants may exceed the size of int");
              space ^^ equals ^^ space ^^ PrintAst.z v
          | None -> empty
        in
        string id ^^ suffix
      ) tags)

and p_qualifier = function
  | Const -> string "const"
  | Volatile -> string "volatile"
  | Restrict -> string "restrict"

and p_qualifiers_break qs =
  if List.length qs > 0 then
    separate_map break1 p_qualifier qs ^^ break1
  else
    empty

and p_type_declarator d =
  let rec p_noptr = function
    | Ident n ->
        string n
    | Array (qs, d, s) ->
        p_noptr d ^^ lbracket ^^ p_qualifiers_break qs ^^ p_expr s ^^ rbracket
    | Function (cc, d, params) ->
        let cc = match cc with Some cc -> print_cc cc ^^ break1 | None -> empty in
        let params =
          if params = [] then
            (* Avoid old-style K&R declarations *)
            string "void"
          else
            separate_map (comma ^^ break 1) (fun (qs, spec, decl) ->
              group (p_qualifiers_break qs ^^ p_type_spec spec ^/^ p_any decl)
            ) params
        in
        group (cc ^^ p_noptr d ^^ parens_with_nesting params)
    | d ->
        lparen ^^ p_any d ^^ rparen
  and p_any = function
    | Pointer (qs, d) ->
        star ^^ p_qualifiers_break qs ^^ p_any d
    | d ->
        p_noptr d
  in
  p_any d

and p_type_name (qs, spec, decl) =
  match decl with
  | Ident "" ->
      p_qualifiers_break qs ^^ p_type_spec spec
  | _ ->
      p_qualifiers_break qs ^^ p_type_spec spec ^^ space ^^ p_type_declarator decl

(* http://en.cppreference.com/w/c/language/operator_precedence *)
and prec_of_op2 op =
  let open Constant in
  match op with
  | AddW | SubW | MultW | DivW -> failwith "[prec_of_op]: should've been desugared"
  | Add -> 4, 4, 4 (* addition is associative in C *)
  | Sub -> 4, 4, 3
  | Div -> 3, 3, 2
  | Mult -> 3, 3, 2
  | Mod -> 3, 3, 2
  | BOr -> 10, 10, 10
  | BAnd ->
      8, 8, 8
  | BXor | Xor -> 9, 9, 9
  | BShiftL | BShiftR ->
      5, 5, 4
  | Eq | Neq -> 7, 7, 6
  | Lt | Lte | Gt | Gte -> 6, 6, 5
  | And -> 11, 11, 11
  | Or -> 12, 12, 12
  | Assign -> 14, 13, 14
  | Comma -> 15, 15, 14
  | PreIncr | PostIncr | PreDecr | PostDecr | Not | BNot | Neg -> raise (Invalid_argument "prec_of_op2")

and prec_of_op1 op =
  let open Constant in
  match op with
  | PreDecr | PreIncr | Not | BNot | Neg -> 2
  | PostDecr | PostIncr -> 1
  | _ -> raise (Invalid_argument "prec_of_op1")

and is_prefix op =
  let open Constant in
  match op with
  | PreDecr | PreIncr | Not | BNot | Neg -> true
  | PostDecr | PostIncr -> false
  | _ -> raise (Invalid_argument ("is_prefix " ^ show_op op))

(* The precedence level [curr] is the maximum precedence the current node should
 * have. If it doesn't, then it should be parenthesized. Lower numbers bind
 * tighter. *)
and paren_if curr mine doc =
  if curr < mine then
    group (lparen ^^ doc ^^ rparen)
  else
    doc

(* [e] is an operand of [op]; is this likely to trigger GCC's -Wparentheses? If
 * so, downgrade the current precedence to 0 to force parentheses. *)
and defeat_Wparentheses op e prec =
  let open Constant in
  if not !Options.parentheses then
    prec
  else match op, e with
  | (BShiftL | BShiftR | BXor | BOr | BAnd), Op2 ((Add | Sub | BOr | BXor | BAnd), _, _) ->
      0
  | Or, Op2 (And, _, _) ->
      0
  | (Lt | Lte | Gt | Gte), Op2 ((Add | Sub), _, _) when !Options.microsoft ->
      0
  | _ ->
      prec

and p_constant w s =
  let suffix = match w with
    | K.UInt64 -> string "ULL"
    | UInt32 | UInt16 | UInt8 | SizeT -> string "U"
    | _ -> empty
  in
  string s ^^ suffix

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
      paren_if curr mine (group (e1 ^/^ print_op op) ^^ group (jump e2))
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
      p_constant w s
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
      let e =
        match e with
        | Type _ -> parens_with_nesting (p_expr' right e)
        | _ ->
            if !Options.parentheses then
              parens_with_nesting (p_expr' right e)
            else
              p_expr' right e
      in
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
      if !Options.microsoft then
        string (match b with
        | false -> "FALSE"
        | true -> "TRUE")
      else
        string (string_of_bool b)
  | CompoundLiteral (t, init) ->
      (* We always parenthesize compound literals no matter what, because GCC
       * parses an application of a function to a compound literal as an n-ary
       * application. *)
      parens_with_nesting (
        (if !Options.cxx17_compat then
          (* C++17 initializer syntax T { ..., ... } *)
          p_type_name t
        else if !Options.cxx_compat then
          (* KRML_CLITERAL works either in C++20 or C11 mode *)
          string "KRML_CLITERAL" ^^ parens (p_type_name t)
        else
          parens (p_type_name t)) ^^
        braces_with_nesting (separate_map (comma ^^ break1) p_init init)
      )
  | MemberAccess (expr, member) ->
      p_expr' 1 expr ^^ dot ^^ string member
  | MemberAccessPointer (expr, member) ->
      p_expr' 1 expr ^^ string "->" ^^ string member
  | InlineComment (s, e, s') ->
      surround 2 1 (p_comment s) (p_expr' curr e) (p_comment s')
  | Stmt stmts ->
      p_stmts stmts
  | CxxInitializerList init ->
      p_init init

and p_comment s =
  if s <> "" then
    (* TODO: escape *)
    string "/* " ^^ nest 2 (flow space (words s)) ^^ string " */"
  else
    empty


and p_expr e = p_expr' 15 e

and p_init (i: init) =
  match i with
  | Designated (Dot _, i) when !Options.cxx17_compat ->
      (* C++17-only syntax: skip designators *)
      p_init i
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
      (* C++20/C11 syntax *)
      dot ^^ string ident
  | Bracket i ->
      lbracket ^^ int i ^^ rbracket

and p_decl_and_init (decl, alignment, init) =
  let post = match alignment with
    | Some t ->
        break1 ^^ p_expr (Call (Name "KRML_POST_ALIGN", [ t ]))
    | None ->
        empty
  in
  group (p_type_declarator decl ^^ post ^^ match init with
    | Some init ->
        space ^^ equals ^^ jump (p_init init)
    | None ->
        empty)

and p_declaration (qs, spec, inline, stor, { maybe_unused; target }, decl_and_inits) =
  let inline =
    match inline with
    | None -> empty
    | Some C11.Inline -> string "inline" ^^ space
    | Some NoInline -> string "KRML_NOINLINE" ^^ space
    | Some MustInline -> string "KRML_MUSTINLINE" ^^ space
  in
  let maybe_unused = if maybe_unused then string "KRML_MAYBE_UNUSED" ^^ space else empty in
  let target = match target with | None -> empty | Some x -> string "KRML_ATTRIBUTE_TARGET" ^^ parens (dquotes (string x)) ^^ break1 in
  let stor = match stor with Some stor -> p_storage_spec stor ^^ space | None -> empty in
  let _, alignment, _ = List.hd decl_and_inits in
  if not (List.for_all (fun (_, a, _) -> a = alignment) decl_and_inits) then
    Warn.fatal_error "In a declarator group, not all declarations have the same \
      alignment, which is not supported for MSVC. Bailing.";
  let pre = match alignment with
    | Some t ->
        p_expr (Call (Name "KRML_PRE_ALIGN", [ t ])) ^^ break1
    | None ->
        empty
  in
  target ^^ pre ^^ maybe_unused ^^ stor ^^ inline ^^ p_qualifiers_break qs ^^ group (p_type_spec spec) ^/^
  separate_map (comma ^^ break 1) p_decl_and_init decl_and_inits


and p_stmt (s: stmt) =
  (* [p_stmt] is responsible for appending [semi] and calling [group]! *)
  match s with
  | Compound stmts ->
      lbrace ^^ nest 2 (hardline ^^ separate_map hardline p_stmt stmts) ^^
      hardline ^^ rbrace
  | Expr expr ->
      group (p_expr expr ^^ semi)
  | Comment s ->
      p_comment s
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
      group (string "if" ^/^ parens_with_nesting (p_expr e)) ^^
      nest_if p_stmt (protect_ite_if_needed stmt)
  | IfElse (e, s1, s2) ->
      group (string "if" ^/^ parens_with_nesting (p_expr e)) ^^
      nest_if p_stmt (protect_solo_if s1) ^^ hardline ^^
      string "else" ^^
      (match s2 with
      | If _ | IfElse _ ->
          space ^^ p_stmt s2
      | _ ->
        nest_if p_stmt s2)
  | IfDef (cond, then_block, elif_blocks, else_block) ->
      let mk_line prefix doc =
        string (KPrint.bsprintf "%s %a" prefix pdoc doc)
      in
      let p stmts = if !Options.microsoft then p_stmt (Compound stmts) else p_stmts stmts in
      group (mk_line "#if" (p_expr cond) ^^ hardline ^^
        p then_block ^^ hardline ^^
        separate_map hardline (fun (cond, stmts) ->
          mk_line "#elif" (p_expr cond) ^^ hardline ^^
          p stmts) elif_blocks ^^
        (if List.length elif_blocks > 0 then hardline else empty) ^^
        (if List.length else_block > 0 then
          string "#else" ^^ hardline ^^
          p else_block ^^ hardline
        else
          empty) ^^
        string "#endif")
  | While (e, s) ->
      group (string "while" ^/^ parens_with_nesting (p_expr e)) ^^
      nest_if p_stmt s
  | Return None ->
      group (string "return" ^^ semi)
  | Return (Some e) ->
      group (string "return" ^^ jump (p_expr e ^^ semi))
  | Decl d ->
      group (p_declaration d ^^ semi)
  | Switch (e, branches, default) ->
      group (string "switch" ^/^ parens_with_nesting (p_expr e)) ^/^
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
  | Continue ->
     string "continue" ^^ semi

and p_stmts stmts = separate_map hardline p_stmt stmts

let p_comments cs =
  separate_map hardline (fun c -> string ("/**\n" ^ c ^ "\n*/")) cs ^^
  if List.length cs > 0 then hardline else empty

let p_microsoft_comments cs =
  separate_map hardline (fun c -> string ("/*++\n" ^ c ^ "\n--*/")) cs ^^
  if List.length cs > 0 then hardline else empty

(* We require infinite width to force this to be rendered on a single line. We
 * then force the rendering of the subexpression on a single line as well. *)
let macro name d: document =
  let c: custom = object (self)
    method requirement = infinity

    method private print o s =
      s.column <- 0;

      o#char '#';
      String.iter o#char "define";
      o#char ' ';
      String.iter o#char name;
      o#char ' ';
      pretty o s 0 true d

    method compact _ =
      failwith "cannot print a macro in compact mode"

    method pretty o s _ _ =
      self#print o s
  end
  in
  custom c

let p_decl_or_function (df: declaration_or_function) =
  match df with
  | Macro (comments, name, def) ->
      let name = String.uppercase_ascii name in
      p_comments comments ^^ macro name (parens (p_expr def))
  | Decl (comments, d) ->
      p_comments comments ^^ group (p_declaration d ^^ semi)
  | Function (comments, d, stmt) ->
      if !Options.microsoft then
        group (p_declaration d) ^/^ p_microsoft_comments comments ^^ p_stmt stmt
      else
        p_comments comments ^^ group (p_declaration d) ^/^ p_stmt stmt
  | Text s ->
      string s

let print_files files =
  PrintCommon.print_files p_decl_or_function files

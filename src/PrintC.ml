(** Pretty-printer that conforms with C syntax. Also defines the grammar of
 * concrete C syntax, as opposed to our idealistic, well-formed C*. *)

open PPrint
open PrintCommon
open C

(* Pretty-printing of actual C syntax *****************************************)

let p_storage_spec = function
  | Typedef -> string "typedef"

let p_expr = function
  | _ -> empty

let rec p_init (i: init) =
  match i with
  | Expr e ->
      p_expr e
  | Initializer inits ->
      braces_with_nesting (separate_map (comma ^^ break 1) p_init inits)

let p_type_spec = function
  | Int w -> print_width w ^^ string "_t"
  | Void -> string "void"
  | Named s -> string s

let p_type_declarator d =
  let rec p_noptr = function
    | Ident n ->
        string n
    | Array (d, s) ->
        p_noptr d ^^ lbracket ^^ p_expr (Constant s) ^^ rbracket
    | Function (d, params) ->
        p_noptr d ^^ lparen ^^ separate_map (comma ^^ space) (fun (spec, decl) ->
          p_type_spec spec ^/^ p_any decl
        ) params ^^ rparen
    | d ->
        lparen ^^ p_any d ^^ rparen
  and p_any = function
    | Pointer d ->
        star ^^ p_any d
    | d ->
        p_noptr d
  in
  p_any d

let p_decl_and_init (decl, init) =
  let init = match init with
    | Some init ->
        break 1 ^^ equals ^/^ p_init init
    | None -> empty
  in
  group (p_type_declarator decl ^^ init)

let p_declaration (spec, stor, decl_and_inits) =
  let stor = match stor with Some stor -> p_storage_spec stor ^^ break 1 | None -> empty in
  stor ^^ group (p_type_spec spec) ^/^
  group (separate_map (comma ^^ break 1) p_decl_and_init decl_and_inits)

let rec p_stmt (s: stmt) =
  (* [p_stmt] is responsible for appending [semi] and calling [group]! *)
  match s with
  | Compound stmts ->
      braces_with_nesting (separate_map hardline p_stmt stmts)
  | Expr expr ->
      group (p_expr expr ^^ semi)
  | SelectIf (e, stmt) ->
      group (string "if" ^/^ p_expr e) ^/^
      braces_with_nesting (p_stmt stmt)
  | SelectIfElse (e, s1, s2) ->
      group (string "if" ^/^ p_expr e) ^/^
      braces_with_nesting (p_stmt s1) ^/^
      string "else" ^/^
      braces_with_nesting (p_stmt s2) 
  | Return None ->
      group (string "return" ^^ semi)
  | Return (Some e) ->
      group (string "return" ^/^ p_expr e ^^ semi)
  | Decl d ->
      group (p_declaration d ^^ semi)


let p_decl_or_function (df: declaration_or_function) =
  match df with
  | Decl d ->
      p_declaration d
  | Function (d, stmt) ->
      group (p_declaration d) ^/^ p_stmt stmt

let print_files =
  PrintCommon.print_files p_decl_or_function

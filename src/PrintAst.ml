(* A pretty-printer for ASTs *)

open Utils
open PPrint
open Ast

module K = Constant

let jump ?(indent=2) body =
  jump indent 1 body

let parens_with_nesting contents =
  surround 2 0 lparen contents rparen

let braces_with_nesting contents =
  surround 2 1 lbrace contents rbrace

let int i = string (string_of_int i)

let arrow = string "->"

(* ------------------------------------------------------------------------ *)

let print_app f head g arguments =
  group (
    f head ^^ jump (
      separate_map (break 1) g arguments
    )
  )

let rec print_program decls =
  separate_map (hardline ^^ hardline) print_decl decls

and print_decl = function
  | DFunction (typ, name, binders, body) ->
      group (string "function" ^/^ string name ^/^ parens_with_nesting (
        separate_map (comma ^^ break 1) print_binder binders
      ) ^^ colon ^/^ print_typ typ) ^/^ braces_with_nesting (
        print_expr body
      )

  | DTypeAlias (name, typ) ->
      group (string "type" ^/^ string name ^/^ equals) ^^
      jump (print_typ typ)

and print_binder { name; typ; mut } =
  group (
    (if mut then string "mutable" ^^ break 1 else empty) ^^
    string name ^^ colon ^/^
    print_typ typ
  )

and print_typ = function
  | TInt w -> print_width w ^^ string "_t"
  | TBuf t -> print_typ t ^^ star
  | TUnit -> string "()"
  | TAlias name -> string name

and print_expr = function
  | EBound v ->
      at ^^ int v
  | EOpen { name; _ } ->
      string name
  | EQualified lident ->
      print_lident lident
  | EConstant c ->
      print_constant c
  | EUnit ->
      string "()"
  | EApp (e, es) ->
      print_app print_expr e print_expr es
  | ELet (binder, e1, e2) ->
      group (string "let" ^/^ print_binder binder ^/^ equals ^^
      jump (print_expr e1) ^/^ string "in") ^/^ print_expr e2
  | EIfThenElse (e1, e2, e3) ->
      string "if" ^/^ print_expr e1 ^/^ string "then" ^^
      jump (print_expr e2) ^/^ string "else" ^^
      jump (print_expr e3)
  | ESequence es ->
      separate_map (semi ^^ hardline) (fun e -> group (print_expr e)) es
  | EAssign (e1, e2) ->
      print_expr e1 ^/^ string "<-" ^/^ print_expr e2
  | EBufCreate (e1, e2) ->
      print_app string "newbuf" print_expr [e1; e2]
  | EBufRead (e1, e2) ->
      print_expr e1 ^^ lbracket ^^ print_expr e2 ^^ rbracket
  | EBufWrite (e1, e2, e3) ->
      print_expr e1 ^^ lbracket ^^ print_expr e2 ^^ rbracket ^/^
      string "<-" ^/^ print_expr e3
  | EBufSub (e1, e2, e3) ->
      print_app string "subbuf" print_expr [e1; e2; e3]
  | EMatch (e, branches) ->
      group (string "match" ^/^ print_expr e ^/^ string "with") ^^
      jump ~indent:0 (print_branches branches)

  | EOp (K.Add, w) -> string "(+," ^^ print_width w ^^ string ")"
  | EOp (K.AddW, w) -> string "(+w," ^^ print_width w ^^ string ")"
  | EOp (K.Sub, w) -> string "(-," ^^ print_width w ^^ string ")"
  | EOp (K.SubW, w) -> string "(-," ^^ print_width w ^^ string ")"
  | EOp (K.Div, w) -> string "(/," ^^ print_width w ^^ string ")"
  | EOp (K.Mult, w) -> string "(*," ^^ print_width w ^^ string ")"
  | EOp (K.Mod, w) -> string "(%," ^^ print_width w ^^ string ")"
  | EOp (K.Or, w) -> string "(|," ^^ print_width w ^^ string ")"
  | EOp (K.And, w) -> string "(&," ^^ print_width w ^^ string ")"
  | EOp (K.Xor, w) -> string "(^," ^^ print_width w ^^ string ")"
  | EOp (K.ShiftL, w) -> string "(<<," ^^ print_width w ^^ string ")"
  | EOp (K.ShiftR, w) -> string "(>>," ^^ print_width w ^^ string ")"

  | ECast (e, t) ->
      parens_with_nesting (print_expr e ^^ colon ^/^ print_typ t)

and print_branches branches =
  separate_map (break 1) (fun b -> group (print_branch b)) branches

and print_branch (pat, expr) =
  group (bar ^^ space ^^ print_pat pat ^^ space ^^ arrow) ^^
  jump ~indent:4 (print_expr expr)

and print_pat = function
  | PUnit ->
      string "()"

and print_constant = function
  | w, s -> string s ^^ print_width w

and print_width = function
  | K.UInt8 -> string "u8"
  | K.UInt16 -> string "u16"
  | K.UInt32 -> string "u32"
  | K.UInt64 -> string "u64"
  | K.Int8 -> string "8"
  | K.Int16 -> string "16"
  | K.Int32 -> string "32"
  | K.Int64 -> string "64"

and print_lident (idents, ident) =
  separate_map dot string (idents @ [ ident ])

let print_files (files: file list) =
  separate_map hardline (fun (f, p) ->
    string (String.uppercase f) ^^ colon ^^ jump (print_program p)
  ) files


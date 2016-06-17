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
  | TInt K.UInt8 -> string "uint8_t"
  | TInt K.UInt16 -> string "uint16_t"
  | TInt K.UInt32 -> string "uint32_t"
  | TInt K.UInt64 -> string "uint64_t"
  | TInt K.Int8 -> string "int8_t"
  | TInt K.Int16 -> string "int16_t"
  | TInt K.Int32 -> string "int32_t"
  | TInt K.Int64 -> string "int64_t"
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

  | EOp K.Add -> string "(+)"
  | EOp K.AddW -> string "(+w)"
  | EOp K.Sub -> string "(-)"
  | EOp K.Div -> string "(/)"
  | EOp K.Mult -> string "(*)"
  | EOp K.Mod -> string "(%)"
  | EOp K.Or -> string "(|)"
  | EOp K.And -> string "(&)"
  | EOp K.Xor -> string "(^)"
  | EOp K.ShiftL -> string "(<<)"
  | EOp K.ShiftR -> string "(>>)"

and print_branches branches =
  separate_map (break 1) (fun b -> group (print_branch b)) branches

and print_branch (pat, expr) =
  group (bar ^^ space ^^ print_pat pat ^^ space ^^ arrow) ^^
  jump ~indent:4 (print_expr expr)

and print_pat = function
  | PUnit ->
      string "()"

and print_constant = function
  | K.UInt8, s -> string s ^^ string "u8"
  | K.UInt16, s -> string s ^^ string "u16"
  | K.UInt32, s -> string s ^^ string "u32"
  | K.UInt64, s -> string s ^^ string "u64"
  | K.Int8, s -> string s ^^ string "8"
  | K.Int16, s -> string s ^^ string "16"
  | K.Int32, s -> string s ^^ string "32"
  | K.Int64, s -> string s ^^ string "64"

and print_lident (idents, ident) =
  separate_map dot string (idents @ [ ident ])

let print_files (files: file list) =
  separate_map hardline (fun (f, p) ->
    string (String.uppercase f) ^^ colon ^^ jump (print_program p)
  ) files


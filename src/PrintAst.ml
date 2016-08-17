(* A pretty-printer for ASTs *)
open PPrint
open PrintCommon
open Ast
open Idents

(* ------------------------------------------------------------------------ *)

let arrow = string "->"

let print_app f head g arguments =
  group (
    f head ^^ jump (
      separate_map (break 1) g arguments
    )
  )

let rec print_decl = function
  | DFunction (typ, name, binders, body) ->
      group (string "function" ^/^ string (string_of_lident name) ^/^ parens_with_nesting (
        separate_map (comma ^^ break 1) print_binder binders
      ) ^^ colon ^/^ print_typ typ) ^/^ braces_with_nesting (
        print_expr body
      )

  | DTypeAlias (name, typ) ->
      group (string "type" ^/^ string (string_of_lident name) ^/^ equals) ^^
      jump (print_typ typ)

  | DGlobal (name, typ, expr) ->
      print_typ typ ^^ space ^^ string (string_of_lident name) ^^ space ^^ equals ^/^ nest 2 (print_expr expr)

and print_binder { name; typ; mut; mark; meta } =
  group (
    (if mut then string "mutable" ^^ break 1 else empty) ^^
    string name ^^ lparen ^^ int mark ^^ comma ^^ space ^^ print_meta meta ^^ rparen ^^ colon ^/^
    print_typ typ
  )

and print_meta = function
  | Some MetaSequence ->
      semi
  | None ->
      empty

and print_typ = function
  | TInt w -> print_width w ^^ string "_t"
  | TBuf t -> print_typ t ^^ star
  | TUnit -> string "()"
  | TQualified name -> string (string_of_lident name)
  | TBool -> string "bool"
  | TAny -> string "any"
  | TArrow (t1, t2) -> print_typ t1 ^^ space ^^ string "->" ^/^ nest 2 (print_typ t2)
  | TZ -> string "mpz_t"

and print_expr = function
  | EAny ->
      string "$any"
  | EAbort ->
      string "$abort"
  | EBound v ->
      at ^^ int v
  | EOpen { name; _ } ->
      bang ^^ string name
  | EQualified lident ->
      print_lident lident
  | EConstant c ->
      print_constant c
  | EUnit ->
      string "()"
  | EApp (e, es) ->
      print_app print_expr e print_expr es
  | ELet (binder, e1, e2) ->
      group (group (string "let" ^/^ print_binder binder ^/^ equals) ^^
      jump (print_expr e1) ^/^ string "in") ^/^ group (print_expr e2)
  | EIfThenElse (e1, e2, e3, t) ->
      string "if" ^/^ print_expr e1 ^/^ string "then" ^^
      jump (print_expr e2) ^/^ string "else" ^^
      jump (print_expr e3) ^/^
      at ^^ print_typ t
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
  | EBufSub (e1, e2) ->
      print_app string "subbuf" print_expr [e1; e2]
  | EBufBlit (e1, e2, e3, e4, e5) ->
      print_app string "blitbuf" print_expr [e1; e2; e3; e4; e5]
  | EMatch (e, branches, t) ->
      group (string "match" ^/^ print_expr e ^/^ string "with") ^^
      jump ~indent:0 (print_branches branches) ^/^
      at ^^ print_typ t
  | EOp (o, w) ->
      string "(" ^^ print_op o ^^ string "," ^^ print_width w ^^ string ")"
  | ECast (e, t) ->
      parens_with_nesting (print_expr e ^^ colon ^/^ print_typ t)
  | EPopFrame ->
      string "pop_frame"
  | EPushFrame ->
      string "push_frame"
  | EBool b ->
      string (string_of_bool b)
  | EReturn e ->
      string "return" ^/^ (nest 2 (print_expr e))

and print_branches branches =
  separate_map (break 1) (fun b -> group (print_branch b)) branches

and print_branch (pat, expr) =
  group (bar ^^ space ^^ print_pat pat ^^ space ^^ arrow) ^^
  jump ~indent:4 (print_expr expr)

and print_pat = function
  | PUnit ->
      string "()"
  | PBool b ->
      string (string_of_bool b)
  | PVar b ->
      print_binder b

let print_files = print_files print_decl

let mk_p f = fun buf t -> PPrint.ToBuffer.compact buf (f t)
let ptyp = mk_p print_typ
let pexpr = mk_p print_expr

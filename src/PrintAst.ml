(* A pretty-printer for ASTs *)
open PPrint
open PrintCommon
open Ast
open Idents

(* ------------------------------------------------------------------------ *)

let arrow = string "->"

let decl_name (d: decl) =
  match d with
  | DFunction (_,lid,_,_)
  | DTypeAlias (lid,_,_)
  | DGlobal (lid,_,_)
  | DTypeFlat (lid,_)
  | DExternal (lid,_) -> lid

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

  | DTypeAlias (name, n, typ) ->
      let args = KList.make n (fun i -> string ("t" ^ string_of_int i)) in
      let args = separate space args in
      group (string "type" ^/^ string (string_of_lident name) ^/^ args ^/^ equals) ^^
      jump (print_typ typ)

  | DExternal (name, typ) ->
      group (string "external" ^/^ string (string_of_lident name) ^/^ colon) ^^
      jump (print_typ typ)

  | DGlobal (name, typ, expr) ->
      print_typ typ ^^ space ^^ string (string_of_lident name) ^^ space ^^ equals ^/^ nest 2 (print_expr expr)

  | DTypeFlat (name, fields) ->
      group (string "flat type" ^/^ string (string_of_lident name) ^/^ equals) ^^
      jump (concat_map (fun (ident, (typ, mut)) ->
        let mut = if mut then string "mutable " else empty in
        group (mut ^^ string ident ^^ colon ^/^ print_typ typ ^^ semi)
      ) fields)

and print_binder { name; typ; mut; meta; mark; _ } =
  group (
    (if mut then string "mutable" ^^ break 1 else empty) ^^
    string name ^^ lparen ^^ int !mark ^^ comma ^^ space ^^ print_meta meta ^^ rparen ^^ colon ^/^
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
  | TBound i -> int i
  | TApp (lid, args) ->
      string (string_of_lident lid) ^/^ separate_map space print_typ args

and print_expr { node; _ } =
  match node with
  | EAny ->
      string "$any"
  | EAbort ->
      string "$abort"
  | EBound v ->
      at ^^ int v
  | EOpen (name, _) ->
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
  | EBufSub (e1, e2) ->
      print_app string "subbuf" print_expr [e1; e2]
  | EBufBlit (e1, e2, e3, e4, e5) ->
      print_app string "blitbuf" print_expr [e1; e2; e3; e4; e5]
  | EMatch (e, branches) ->
      group (string "match" ^/^ print_expr e ^/^ string "with") ^^
      jump ~indent:0 (print_branches branches)
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
  | EFlat fields ->
      braces_with_nesting (separate_map break1 (fun (name, expr) ->
        group (string name ^/^ equals ^/^ print_expr expr ^^ semi)
      ) fields)
  | EField (expr, field) ->
      parens_with_nesting (print_expr expr) ^^ dot ^^ string field
  | EWhile (e1, e2) ->
      string "while" ^/^ parens_with_nesting (print_expr e1) ^/^
      braces_with_nesting (print_expr e2)
  | EBufCreateL es ->
      string "newbuf" ^/^ braces_with_nesting (separate_map (comma ^^ break1) print_expr es)


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

let ptyp = printf_of_pprint print_typ
let pexpr = printf_of_pprint print_expr
let plid = printf_of_pprint print_lident
let pdecl = printf_of_pprint_pretty print_decl
let pop = printf_of_pprint_pretty print_op

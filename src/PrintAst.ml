(* A pretty-printer for ASTs *)
open PPrint
open PrintCommon
open Ast
open Idents
open Common

(* ------------------------------------------------------------------------ *)

let arrow = string "->"
let lambda = fancystring "λ" 1

let print_app f head g arguments =
  group (
    f head ^^ jump (
      separate_map (break 1) g arguments
    )
  )

let rec print_decl = function
  | DFunction (cc, flags, n, typ, name, binders, body) ->
      let cc = match cc with Some cc -> print_cc cc ^^ break1 | None -> empty in
      print_comment flags ^^
      cc ^^ print_flags flags ^^ group (string "function" ^/^ string (string_of_lident name) ^/^
      langle ^^ int n ^^ rangle ^^
      parens_with_nesting (
        separate_map (comma ^^ break 1) print_binder binders
      ) ^^ colon ^/^ print_typ typ) ^/^ braces_with_nesting (
        print_expr body
      )

  | DExternal (cc, name, typ) ->
      let cc = match cc with Some cc -> print_cc cc ^^ break1 | None -> empty in
      group (cc ^^ string "external" ^/^ string (string_of_lident name) ^/^ colon) ^^
      jump (print_typ typ)

  | DGlobal (flags, name, typ, expr) ->
      print_flags flags ^^ print_typ typ ^^ space ^^ string (string_of_lident name) ^^ space ^^ equals ^/^ nest 2 (print_expr expr)

  | DType (name, flags, n, def, _) ->
      let args = KList.make n (fun i -> string ("t" ^ string_of_int i)) in
      let args = separate space args in
      group (string "type" ^/^ print_flags flags ^/^ string (string_of_lident name) ^/^ args ^/^ equals) ^^
      jump (print_type_def def)
| DTypeMutual (ty_decls) ->
      separate_map (string "and" ^^ break1) (fun decl -> print_decl decl) ty_decls

and print_comment flags =
  match KList.find_opt (function Comment c -> Some c | _ -> None) flags with
  | Some c ->
      string "(*" ^^ string c ^^ string "*)" ^^ hardline
  | None ->
      empty

and print_type_def = function
  | Flat fields ->
      string "flat" ^/^
      braces_with_nesting (print_fields_opt_t fields)

  | Variant branches ->
      string "data" ^^
      let branches = List.map (fun (ident, fields) ->
        string ident ^/^ braces_with_nesting (print_fields_t fields)
      ) branches in
      jump ~indent:0 (ifflat empty (bar ^^ space) ^^ separate (break 1 ^^ bar ^^ space) branches)

  | Enum tags ->
      string "enum" ^/^
        braces_with_nesting (separate_map (comma ^^ break1) (fun lid ->
          string (string_of_lident lid)
        ) tags)

  | Union fields ->
      string "union" ^/^ braces_with_nesting
        (separate_map (semi ^^ hardline) (fun (name, t) -> group (
            string name ^/^ equals ^^ break1
          ) ^^ print_typ t)
        fields)

  | Abbrev typ ->
      string "abbrev" ^/^
      jump (print_typ typ)

and print_fields_t fields =
  separate_map (semi ^^ break1) (fun (ident, (typ, mut)) ->
    let mut = if mut then string "mutable " else empty in
    group (group (mut ^^ string ident ^^ colon) ^/^ print_typ typ)
  ) fields

and print_fields_opt_t fields =
  separate_map (semi ^^ break1) (fun (ident, (typ, mut)) ->
    let ident = if ident = None then empty else string (Option.must ident) in
    let mut = if mut then string "mutable " else empty in
    group (group (mut ^^ ident ^^ colon) ^/^ print_typ typ)
  ) fields

and print_flags flags =
  separate_map space print_flag flags

and print_flag = function
  | Private ->
      string "private"
  | NoExtract ->
      string "noextract"
  | CInline ->
      string "c_inline"
  | Substitute ->
      string "substitute"
  | GcType ->
      string "gc_type"
  | Comment _ ->
      empty

and print_binder { typ; node = { name; mut; meta; mark; _ }} =
  (if mut then string "mutable" ^^ break 1 else empty) ^^
  group (string name ^^ lparen ^^ int !mark ^^ comma ^^ space ^^ print_meta meta ^^
  rparen ^^ colon) ^/^
  nest 2 (print_typ typ)

and print_meta = function
  | Some MetaSequence ->
      semi
  | None ->
      empty

and print_typ_paren = function
  | TArrow _ as t ->
      parens_with_nesting (print_typ t)
  | t ->
      print_typ t

and print_typ = function
  | TInt w -> print_width w ^^ string "_t"
  | TBuf t -> print_typ t ^^ star
  | TArray (t, k) -> print_typ t ^^ lbracket ^^ print_constant k ^^ rbracket
  | TUnit -> string "()"
  | TQualified name -> string (string_of_lident name)
  | TBool -> string "bool"
  | TAny -> string "any"
  | TArrow (t1, t2) -> print_typ_paren t1 ^^ space ^^ string "->" ^/^ nest 2 (print_typ t2)
  | TBound i -> int i
  | TApp (lid, args) ->
      string (string_of_lident lid) ^/^ separate_map space print_typ args
  | TTuple ts ->
      separate_map (space ^^ star ^^ space) print_typ ts
  | TAnonymous t ->
      print_type_def t

and print_lifetime = function
  | Stack -> string "stack"
  | Eternal -> string "eternal"

and print_let_binding (binder, e1) =
  group (group (string "let" ^/^ print_binder binder ^/^ equals) ^^
  jump (print_expr e1))

and print_expr { node; _ } =
  match node with
  | EComment (s, e, s') ->
      surround 2 1 (string s) (print_expr e) (string s')
  | EAny ->
      string "$any"
  | EAbort s ->
      string "$abort" ^^
      (match s with None -> empty | Some s -> string " (" ^^ string s ^^ string ")")
  | EIgnore e ->
      print_app string "ignore" print_expr [ e ]
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
  | EString s ->
      dquote ^^ string s ^^ dquote
  | EApp (e, es) ->
      print_app print_expr e print_expr es
  | ETApp (e, ts) ->
      print_app print_expr e (fun t -> group (langle ^/^ print_typ t ^/^ rangle)) ts
  | ELet (binder, e1, e2) ->
      group (print_let_binding (binder, e1) ^/^ string "in") ^/^ group (print_expr e2)
  | EIfThenElse (e1, e2, e3) ->
      string "if" ^/^ print_expr e1 ^/^ string "then" ^^
      jump (print_expr e2) ^/^ string "else" ^^
      jump (print_expr e3)
  | ESequence es ->
      separate_map (semi ^^ hardline) (fun e -> group (print_expr e)) es
  | EAssign (e1, e2) ->
      group (print_expr e1 ^/^ string "<-") ^^ (jump (print_expr e2))
  | EBufCreate (l, e1, e2) ->
      print_lifetime l ^^ space ^^
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
  | EBufFill (e1, e2, e3) ->
      print_app string "fillbuf" print_expr [e1; e2; e3 ]
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
  | EBreak ->
      string "break"
  | EReturn e ->
      string "return" ^/^ (nest 2 (print_expr e))
  | EFlat fields ->
      braces_with_nesting (separate_map break1 (fun (name, expr) ->
        let name = match name with Some name -> string name | None -> empty in
        group (name ^/^ equals ^/^ print_expr expr ^^ semi)
      ) fields)
  | EField (expr, field) ->
      parens_with_nesting (print_expr expr) ^^ dot ^^ string field
  | EWhile (e1, e2) ->
      string "while" ^/^ parens_with_nesting (print_expr e1) ^/^
      braces_with_nesting (print_expr e2)
  | EFor (binder, e1, e2, e3, e4) ->
      string "for" ^/^ parens_with_nesting (
        print_let_binding (binder, e1) ^^
        semi ^/^
        separate_map (semi ^^ break1) print_expr [ e2; e3 ]) ^/^
      braces_with_nesting (print_expr e4)
  | EBufCreateL (l, es) ->
      print_lifetime l ^/^
      string "newbuf" ^/^ braces_with_nesting (separate_map (comma ^^ break1) print_expr es)
  | ECons (ident, es) ->
      string ident ^/^
      if List.length es > 0 then
        parens_with_nesting (separate_map (comma ^^ break1) print_expr es)
      else
        empty
  | ETuple es ->
      parens_with_nesting (separate_map (comma ^^ break1) print_expr es)
  | EEnum lid ->
      string (string_of_lident lid)
  | ESwitch (e, branches) ->
      string "switch" ^^ space ^^ print_expr e ^/^ braces_with_nesting (
        separate_map hardline (fun (lid, e) ->
          string "case" ^^ space ^^ string (string_of_lident lid) ^^ colon ^^
          nest 2 (hardline ^^ print_expr e)
        ) branches)
  | EFun (binders, body, t) ->
      string "fun" ^/^ parens_with_nesting (
        separate_map (comma ^^ break 1) print_binder binders
      ) ^/^ colon ^^ group (print_typ t) ^/^ braces_with_nesting (
        print_expr body
      )
  | EAddrOf e ->
      ampersand ^^ print_expr e



and print_branches branches =
  separate_map (break 1) (fun b -> group (print_branch b)) branches

and print_branch (binders, pat, expr) =
  group (bar ^^ space ^^
    lambda ^^
    separate_map (comma ^^ break 1) print_binder binders ^^
    dot ^^ space ^^
    print_pat pat ^^ space ^^ arrow
  ) ^^ jump ~indent:4 (print_expr expr)

and print_pat p =
  match p.node with
  | PWild ->
      string "_"
  | PUnit ->
      string "()"
  | PBool b ->
      string (string_of_bool b)
  | PBound b ->
      at ^^ int b
  | POpen (i, _) ->
      bang ^^ string i
  | PCons (ident, pats) ->
      string ident ^/^ parens_with_nesting (separate_map (comma ^^ break1) print_pat pats)
  | PRecord fields ->
      braces_with_nesting (separate_map break1 (fun (name, pat) ->
        group (string name ^/^ equals ^/^ print_pat pat ^^ semi)
      ) fields)
  | PTuple ps ->
      parens_with_nesting (separate_map (comma ^^ break1) print_pat ps)
  | PEnum lid ->
      string (string_of_lident lid)
  | PDeref p ->
      star ^^ print_pat p

let print_files = print_files print_decl

module Ops = struct
  let ploc = printf_of_pprint Location.print_location
  let ptyp = printf_of_pprint print_typ
  let pptyp = printf_of_pprint_pretty print_typ
  let pexpr = printf_of_pprint print_expr
  let ppexpr = printf_of_pprint_pretty print_expr
  let plid = printf_of_pprint print_lident
  let pplid = printf_of_pprint_pretty print_lident
  let pdecl = printf_of_pprint print_decl
  let ppdecl = printf_of_pprint_pretty print_decl
  let pdef = printf_of_pprint print_type_def
  let ppdef = printf_of_pprint_pretty print_type_def
  let pop = printf_of_pprint print_op
  let ppop = printf_of_pprint_pretty print_op
  let ppat = printf_of_pprint print_pat
  let pppat = printf_of_pprint_pretty print_pat
  let plb = printf_of_pprint print_let_binding
  let pplb = printf_of_pprint_pretty print_let_binding
  let plbs buf lbs = List.iter (plb buf) lbs
  let pplbs buf lbs = List.iter (pplb buf) lbs
end

include Ops

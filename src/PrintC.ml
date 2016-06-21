(** Pretty-printer that conforms with C syntax. Also defines the grammar of
 * concrete C syntax, as opposed to our idealistic, well-formed C*. *)

open PPrint
open PrintCommon
open C

(* Actual C grammar ***********************************************************)

(* This pretty-printer based on: http:/ /en.cppreference.com/w/c/language/declarations 
 * Many cases are omitted from this bare-bones C grammar; hopefully, to be extended. *)
type c_type_spec =
  | Int of Constant.width
  | Void
  | Named of c_ident

and c_storage_spec =
  | Typedef

and c_decl_and_init =
  c_decl * c_init option

and c_decl_and_inits =
  c_decl_and_init list

and c_decl =
  | Ident of c_ident
  | Pointer of c_decl
  | Array of c_decl * int
  | Function of c_decl * c_params

and c_expr =
  (* TODO *)
  C.expr

and c_params =
  (* No support for old syntax, e.g. K&R, or [void f(void)]. *)
  c_param list

and c_param =
  c_type_spec * c_decl

and c_ident =
  string

and c_init =
  | Expr of c_expr
  | Initializer of c_init list


(* Pretty-printing of actual C syntax *****************************************)

let print_c_storage_spec = function
  | Typedef -> string "typedef"

let _print_c_expr = ref (fun _ -> assert false)
let print_c_expr e =
  (* TODO *)
  !_print_c_expr e

let print_init = function
  | Expr e ->
      print_c_expr e
  | _ ->
      failwith "[print_init]: TODO"

let print_type_spec = function
  | Int w -> print_width w ^^ string "_t"
  | Void -> string "void"
  | Named s -> string s

let print_type_decl d =
  let rec p_noptr = function
    | Ident n ->
        string n
    | Array (d, s) ->
        p_noptr d ^^ lbracket ^^ int s ^^ rbracket
    | Function (d, params) ->
        p_noptr d ^^ lparen ^^ separate_map (comma ^^ space) (fun (spec, decl) ->
          print_type_spec spec ^/^ p_any decl
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

let print_decl_and_init (decl, init) =
  let init = match init with
    | Some init ->
        break 1 ^^ equals ^/^ print_init init
    | None -> empty
  in
  group (print_type_decl decl ^^ init)

(* Omitting type qualifiers and alignment specifiers. *)
let print_c_decl (spec: c_type_spec) ?(stor:c_storage_spec option) (decl_and_inits: c_decl_and_inits) =
  let stor = match stor with Some stor -> print_c_storage_spec stor ^^ break 1 | None -> empty in
  stor ^^ group (print_type_spec spec) ^/^
  group (separate_map (comma ^^ break 1) print_decl_and_init decl_and_inits)


(* Helpers to convert from C* to actual C syntax ******************************)

(* Turns the ML declaration inside-out to match the C reading of a type. *)
let mk_spec_and_decl, mk_spec_and_decl_f =
  let rec mk name (t: typ) (k: c_decl -> c_decl): c_type_spec * c_decl =
    match t with
    | Pointer t ->
        mk name t (fun d -> Pointer (k d))
    | Array (t, size) ->
        mk name t (fun d -> Array (k d, size))
    | Function (t, ts) ->
        mk name t (fun d -> Function (k d, List.map (fun t -> mk "" t (fun d -> d)) ts))
    | Int w ->
        Int w, k (Ident name)
    | Void ->
        Void, k (Ident name)
    | Named n ->
        Named n, k (Ident name)
  in
  (fun name t ->
    mk name t (fun d -> d)),
  (fun name ret_t params ->
    mk name ret_t (fun d -> Function (d, List.map (fun (n, t) -> mk n t (fun d -> d)) params)))


(* Using helpers, converts from C* to actual C grammar and prints it **********)
let brace_if b f x =
  if b then
    braces_with_nesting (f x)
  else
    jump (f x)

let rec print_cstar_stmt = function
  | Return e ->
      string "return" ^/^ print_cstar_expr e ^^ semi
  | Ignore e ->
      print_cstar_expr e ^^ semi
  | Decl (binder, e) ->
      let spec, decl = mk_spec_and_decl binder.name binder.typ in
      print_c_decl spec [ decl, Some (Expr e) ] ^^ semi
  | IfThenElse (e, b1, b2) ->
      string "if" ^/^ lparen ^^ print_cstar_expr e ^^ rparen ^/^ string "then" ^^
      brace_if (List.length b1 > 1) print_cstar_block b1 ^/^ string "else" ^^
      brace_if (List.length b2 > 1) print_cstar_block b2
  | Assign (e1, e2) ->
      print_cstar_expr e1 ^/^ equals ^/^ print_cstar_expr e2 ^^ semi
  | BufWrite (e1, e2, e3) ->
      print_cstar_expr e1 ^^ lbracket ^^ print_cstar_expr e2 ^^ rbracket ^/^ equals ^/^
      print_cstar_expr e3 ^^ semi

and print_cstar_block stmts =
  separate_map hardline (fun s -> group (print_cstar_stmt s)) stmts

and print_cstar_expr = function
  | _ -> empty

let _horrible_hack =
  _print_c_expr := print_cstar_expr

let print_cstar_decl = function
  | TypeAlias (name, t) ->
      let spec, decl = mk_spec_and_decl name t in
      group (print_c_decl spec ~stor:Typedef [ decl, None ] ^^ semi)

  | Function (return_type, name, parameters, body) ->
      let parameters = List.map (fun { name; typ } -> name, typ) parameters in
      let spec, decl = mk_spec_and_decl_f name return_type parameters in
      group (print_c_decl spec [ decl, None ]) ^/^
      braces_with_nesting (print_cstar_block body)

let print_files = print_files print_cstar_decl

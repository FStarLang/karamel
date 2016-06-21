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

let print_init _ =
  failwith "TODO"

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
        ) params
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
  print_type_decl decl ^^ init

(* Omitting type qualifiers and alignment specifiers. *)
let print_c_decl (spec: c_type_spec) ?(stor:c_storage_spec option) (decl_and_inits: c_decl_and_inits) =
  let stor = match stor with Some stor -> print_c_storage_spec stor ^^ break 1 | None -> empty in
  stor ^^ print_type_spec spec ^/^
  separate_map (comma ^^ break 1) print_decl_and_init decl_and_inits


(* Helpers to convert from C* to actual C *************************************)

(* Turns the ML declaration inside-out to match the C reading of a type. *)
let mk_spec_and_decl name (t: typ): c_type_spec * c_decl =
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
  mk name t (fun d -> d)


(* C* to actual C grammar + pretty printing ***********************************)

let rec print_cstar_decl = function
  | TypeAlias (name, t) ->
      let spec, decl = mk_spec_and_decl name t in
      print_c_decl spec ~stor:Typedef [ decl, None ]

  | Function (return_type, name, parameters, body) ->
      empty


let print_files = print_files print_cstar_decl

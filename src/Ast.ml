(** Definition of the input format. *)

open Utils

(** The input AST. Note: F* doesn't have flat data constructors, so we need to introduce
 * (inefficient) boxing for the sake of interop. *)

type program =
  decl list

and decl =
  | DFunction of (typ * ident * binder list * expr)
  | DTypeAlias of (ident * typ)

and expr =
  | EBound of var
  | EOpen of binder
  | EQualified of lident
  | EConstant of Constant.t
  | EUnit
  | EApp of (expr * expr list)
  | ELet of (binder * expr * expr)
  | EIfThenElse of (expr * expr * expr)
  | ESequence of expr list
  | EAssign of (expr * expr)
    (** left expression can only be a EBound of EOpen *)
  | EBufCreate of (expr * expr)
  | EBufRead of (expr * expr)
  | EBufWrite of (expr * expr * expr)
  | EBufSub of (expr * expr * expr)
  | EMatch of (expr * branches)
  | EOp of op

and op = Add | AddW | Sub | Div | Mult | Mod | Or | And | Xor | ShiftL | ShiftR

and branches =
  branch list

and branch =
  pattern * expr

and pattern =
  | PUnit

and var =
  int (** a De Bruijn index *)

and binder = {
  name: ident;
  typ: typ;
  mut: bool;
}

and ident =
  string (** for pretty-printing *)

and lident =
  ident list * ident

and typ =
  | TInt of Constant.width
  | TBuf of typ
  | TUnit
  | TAlias of ident

(** Versioned binary writing/reading of ASTs *)

type version = int
let current_version: version = 1

type file = string * program
type binary_format = version * file list


(** Some visitors for our AST of expressions *)

class virtual ['env, 'result] visitor = object (self)

  (* This method, whose default implementation is the identity,
     can be used to extend the environment when a binding is
     entered. *)
  method extend (env: 'env) (_: binder): 'env =
    env

  (* The main visitor method inspects the structure of [ty] and
     dispatches control to the appropriate case method. *)
  method visit (env: 'env) (e: expr): 'result =
    match e with
    | EBound var ->
        self#ebound env var
    | EOpen binder ->
        self#eopen env binder
    | EQualified lident ->
        self#equalified env lident
    | EConstant c ->
        self#econstant env c
    | EUnit ->
        self#eunit env
    | EApp (e, es) ->
        self#eapp env e es
    | ELet (b, e1, e2) ->
        self#elet env b e1 e2
    | EIfThenElse (e1, e2, e3) ->
        self#eifthenelse env e1 e2 e3
    | ESequence es ->
        self#esequence env es
    | EAssign (e1, e2) ->
        self#eassign env e1 e2
    | EBufCreate (e1, e2) ->
        self#ebufcreate env e1 e2
    | EBufRead (e1, e2) ->
        self#ebufread env e1 e2
    | EBufWrite (e1, e2, e3) ->
        self#ebufwrite env e1 e2 e3
    | EBufSub (e1, e2, e3) ->
        self#ebufsub env e1 e2 e3
    | EMatch (e, branches) ->
        self#ematch env e branches
    | EOp op ->
        self#eop env op

  method virtual ebound: 'env -> var -> 'result
  method virtual eopen: 'env -> binder -> 'result
  method virtual equalified: 'env -> lident -> 'result
  method virtual econstant: 'env -> Constant.t -> 'result
  method virtual eunit: 'env -> 'result
  method virtual eapp: 'env -> expr -> expr list -> 'result
  method virtual elet: 'env -> binder -> expr -> expr -> 'result
  method virtual eifthenelse: 'env -> expr -> expr -> expr -> 'result
  method virtual esequence: 'env -> expr list -> 'result
  method virtual eassign: 'env -> expr -> expr -> 'result
  method virtual ebufcreate: 'env -> expr -> expr -> 'result
  method virtual ebufread: 'env -> expr -> expr -> 'result
  method virtual ebufwrite: 'env -> expr -> expr -> expr -> 'result
  method virtual ebufsub: 'env -> expr -> expr -> expr -> 'result
  method virtual ematch: 'env -> expr -> branches -> 'result
  method virtual eop: 'env -> op -> 'result

end


class ['env] map = object (self)

  inherit ['env, expr] visitor

  method ebound _env var =
    EBound var

  method eopen _env binder =
    EOpen binder

  method equalified _env lident =
    EQualified lident

  method econstant _env constant =
    EConstant constant

  method eunit _env =
    EUnit

  method eapp env e es =
    EApp (self#visit env e, List.map (self#visit env) es)

  method elet env b e1 e2 =
    ELet (b, self#visit env e1, self#visit (self#extend env b) e2)

  method eifthenelse env e1 e2 e3 =
    EIfThenElse (self#visit env e1, self#visit env e2, self#visit env e3)

  method esequence env es =
    ESequence (List.map (self#visit env) es)

  method eassign env e1 e2 =
    EAssign (self#visit env e1, self#visit env e2)

  method ebufcreate env e1 e2 =
    EBufCreate (self#visit env e1, self#visit env e2)

  method ebufread env e1 e2 =
    EBufRead (self#visit env e1, self#visit env e2)

  method ebufwrite env e1 e2 e3 =
    EBufWrite (self#visit env e1, self#visit env e2, self#visit env e3)

  method ebufsub env e1 e2 e3 =
    EBufSub (self#visit env e1, self#visit env e2, self#visit env e3)

  method ematch env e branches =
    EMatch (self#visit env e, self#branches env branches)

  method eop env o =
    EOp o

  method branches env branches =
    List.map (fun (pat, expr) ->
      pat, self#visit env expr
    ) branches

end

(** Input / output of ASTs *)

let read_file (f: string): file list =
  let contents: binary_format = with_open_in f input_value in
  let version, files = contents in
  if version <> current_version then
    failwith "This file is for an older version of KreMLin";
  files

let write_file (files: file list) (f: string): unit =
  with_open_out f (fun oc ->
    output_value oc (current_version, files);
  )


module Print = struct
  (** A few helpers stolen from Mezzo's source code and François' extra PPrint combinators. *)
  open PPrint

  (** Sniff the size of the terminal for optimal use of the width. *)
  let theight, twidth =
    let height, width = ref 0, ref 0 in
    match
      Scanf.sscanf (run_and_read "stty" [|"size"|]) "%d %d" (fun h w ->
        height := h;
        width := w);
      !height, !width
    with
    | exception _ ->
        24, 80
    | 0, 0 ->
        24, 80
    | h, w ->
        h, w

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
    | TInt Constant.UInt8 -> string "uint8"
    | TInt Constant.UInt16 -> string "uint16"
    | TInt Constant.UInt32 -> string "uint32"
    | TInt Constant.UInt64 -> string "uint64"
    | TInt Constant.Int8 -> string "int8"
    | TInt Constant.Int16 -> string "int16"
    | TInt Constant.Int32 -> string "int32"
    | TInt Constant.Int64 -> string "int64"
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

    | EOp Add -> string "(+)"
    | EOp AddW -> string "(+w)"
    | EOp Sub -> string "(-)"
    | EOp Div -> string "(/)"
    | EOp Mult -> string "(*)"
    | EOp Mod -> string "(%)"
    | EOp Or -> string "(|)"
    | EOp And -> string "(&)"
    | EOp Xor -> string "(^)"
    | EOp ShiftL -> string "(<<)"
    | EOp ShiftR -> string "(>>)"

  and print_branches branches =
    separate_map (break 1) (fun b -> group (print_branch b)) branches

  and print_branch (pat, expr) =
    group (bar ^^ space ^^ print_pat pat ^^ space ^^ arrow) ^^
    jump ~indent:4 (print_expr expr)

  and print_pat = function
    | PUnit ->
        string "()"

  and print_constant = function
    | Constant.UInt8, s -> string s ^^ string "u8"
    | Constant.UInt16, s -> string s ^^ string "u16"
    | Constant.UInt32, s -> string s ^^ string "u32"
    | Constant.UInt64, s -> string s ^^ string "u64"
    | Constant.Int8, s -> string s ^^ string "8"
    | Constant.Int16, s -> string s ^^ string "16"
    | Constant.Int32, s -> string s ^^ string "32"
    | Constant.Int64, s -> string s ^^ string "64"

  and print_lident (idents, ident) =
    separate_map dot string (idents @ [ ident ])

  let print_files (files: file list) =
    separate_map hardline (fun (f, p) ->
      string (String.uppercase f) ^^ colon ^^ jump (print_program p)
    ) files

  let render doc =
    let buf = Buffer.create 1024 in
    PPrint.ToBuffer.pretty 0.95 twidth buf doc;
    Buffer.contents buf

  let print doc =
    PPrint.ToChannel.pretty 0.95 twidth stdout doc

end

(** Definition of the input format. *)

open Utils

(** The input AST *)

type program =
  decl list

and decl =
  | DFunction of typ * ident * binder list * expr

and expr =
  | EBound of var
  | EOpen of binder
  | EQualified of lident
  | EConstant of constant
  | EUnit
  | EApp of expr * expr list
  | ELet of binder * expr * expr
  | EIfThenElse of expr * expr * expr
  | ESequence of expr * expr
  | EAssign of expr * expr
    (** left expression can only be a EBound of EOpen *)
  | EBufCreate of expr * expr
  | EBufRead of expr * expr
  | EBufWrite of expr * expr * expr
  | EBufSub of expr * expr * expr

and constant =
  | CInt of string

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
  | TInt32
  | TBuf of typ
  | TUnit

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
    | ESequence (e1, e2) ->
        self#esequence env e1 e2
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

  method virtual ebound: 'env -> var -> 'result
  method virtual eopen: 'env -> binder -> 'result
  method virtual equalified: 'env -> lident -> 'result
  method virtual econstant: 'env -> constant -> 'result
  method virtual eunit: 'env -> 'result
  method virtual eapp: 'env -> expr -> expr list -> 'result
  method virtual elet: 'env -> binder -> expr -> expr -> 'result
  method virtual eifthenelse: 'env -> expr -> expr -> expr -> 'result
  method virtual esequence: 'env -> expr -> expr -> 'result
  method virtual eassign: 'env -> expr -> expr -> 'result
  method virtual ebufcreate: 'env -> expr -> expr -> 'result
  method virtual ebufread: 'env -> expr -> expr -> 'result
  method virtual ebufwrite: 'env -> expr -> expr -> expr -> 'result
  method virtual ebufsub: 'env -> expr -> expr -> expr -> 'result

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

  method esequence env e1 e2 =
    ESequence (self#visit env e1, self#visit env e2)

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

end

(** Input / output of ASTs *)

let read_file (f: string): program =
  let contents: binary_format = with_open_in f input_value in
  let version, program = contents in
  if version <> current_version then
    failwith "This file is for an older version of KreMLin";
  program

let write_file (p: program) (f: string): unit =
  with_open_out f (fun oc ->
    output_value oc (current_version, p);
  )


module Print = struct
  (** A few helpers stolen from Mezzo's source code and François' extra PPrint combinators. *)
  open PPrint

  (** Sniff the size of the terminal for optimal use of the width. *)
  let theight, twidth =
    let height, width = ref 0, ref 0 in
    match
      Scanf.sscanf (run_and_read "stty size") "%d %d" (fun h w ->
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
  ;;

  let jump ?(indent=2) body =
    jump indent 1 body

  let parens_with_nesting contents =
    surround 2 0 lparen contents rparen

  let braces_with_nesting contents =
    surround 2 1 lbrace contents rbrace

  let int i = string (string_of_int i)

  (* ------------------------------------------------------------------------ *)

  let rec print_program decls =
    separate_map (hardline ^^ hardline) print_decl decls

  and print_decl = function
    | DFunction (name, binders, body) ->
        string "function" ^/^ parens_with_nesting (
          separate_map (comma ^^ break 1) print_binder binders
        ) ^/^ braces_with_nesting (
          print_expr body
        )

  and print_binder { name; typ; mut } =
    group (
      if mut then string "mutable" else empty ^/^
      string name ^^ colon ^/^
      print_typ typ
    )

  and print_typ = function
    | TInt32 ->
        string "int32"
    | TBuf t ->
        print_typ t ^^ star

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
        print_app (print_expr e) es
    | ELet (binder, e1, e2) ->
        string "let" ^/^ print_binder binder ^/^ equals ^/^
        jump (print_expr e1) ^/^ string "in" ^/^ print_expr e2
    | EIfThenElse (e1, e2, e3) ->
        string "if" ^/^ print_expr e1 ^/^ string "then" ^/^
        jump (print_expr e2) ^/^ string "else" ^/^
        jump (print_expr e3)
    | ESequence (e1, e2) ->
        print_expr e1 ^^ semi ^^ hardline ^^ print_expr e2
    | EAssign (e1, e2) ->
        print_expr e1 ^/^ string "<-" ^/^ print_expr e2
    | EBufCreate (e1, e2) ->
        print_app (string "newbuf") [e1; e2]
    | EBufRead (e1, e2) ->
        print_expr e1 ^^ lbracket ^^ print_expr e2 ^^ rbracket
    | EBufWrite (e1, e2, e3) ->
        print_expr e1 ^^ lbracket ^^ print_expr e2 ^^ rbracket ^/^
        string "<-" ^/^ print_expr e3
    | EBufSub (e1, e2, e3) ->
        print_app (string "subbuf") [e1; e2; e3]

  and print_app e es =
    prefix 2 1 e (separate_map (break 1) print_expr es)

  and print_constant = function
    | CInt i ->
        string (Z.to_string i)

  and print_lident (idents, ident) =
    separate_map dot string (idents @ [ ident ])

end

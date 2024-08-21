(* We go directly from MiniRust to a rendering. Mostly, on the basis that
   MiniRust is close to actual Rust that we can print out syntax on the fly
   (unlike C, where for instance the types are so different that we need to have
   a different AST before going to print). *)

open PPrint
open PrintCommon
open MiniRust

module NameMap = Map.Make(struct
  type t = name
  let compare = compare
end)

let is_expression_with_block e =
  match e with
  | IfThenElse _ | For _ | While _ -> true
  | _ -> false

type env = {
  vars: [ `Named of string | `GoneUnit ] list;
  type_vars: string list;
  prefix: string list;
  debug: bool;
  globals: name NameMap.t;
}

let lexical_conventions x =
  let dst = Buffer.create 128 in
  String.iteri (fun i c ->
    let cp = Uchar.of_char c in
    let is_valid =
      if i = 0 then
        Uucp.Id.is_xid_start cp || c = '_'
      else
        Uucp.Id.is_xid_continue cp
    in
    if is_valid then
      Buffer.add_utf_8_uchar dst cp
    else
      Buffer.add_utf_8_uchar dst (Uchar.of_int 0xb7)
  ) x;
  Buffer.contents dst

let mk_uniq { vars; _ } x =
  if not (List.mem (`Named x) vars) then
    x
  else
    let i = ref 0 in
    let attempt () = x ^ string_of_int !i in
    while List.mem (`Named (attempt ())) vars do incr i done;
    attempt ()

let avoid_keywords (x: string) =
  let keywords = [
    "as"; "break"; "const"; "continue"; "crate"; "else"; "enum"; "extern";
    "false"; "fn"; "for"; "if"; "impl"; "in"; "let"; "loop"; "match"; "mod";
    "move"; "mut"; "pub"; "ref"; "return"; "self"; "Self"; "static"; "struct";
    "super"; "trait"; "true"; "type"; "unsafe"; "use"; "where"; "while";
    "async"; "await"; "dyn"; "abstract"; "become"; "box"; "do"; "final";
    "macro"; "override"; "priv"; "typeof"; "unsized"; "virtual"; "yield"; "try";
  ] in
  if List.mem x keywords then "r#" ^ x else x

let allocate_name env x =
  avoid_keywords (mk_uniq env (lexical_conventions x))

let push env x =
  let x =
    match x with
    | `Named _ when List.mem x env.vars ->
        failwith "impossible: unexpected shadowing, please call mk_uniq"
    | _ ->
        x
  in
  { env with vars = x :: env.vars }

let rec register_global env source_name =
  let source_prefix, source_final = KList.split_at_last source_name in
  (* There might be collisions in the source. This is neither optimal nor
     correct. *)
  if NameMap.mem source_name env.globals then
    register_global env (source_prefix @ [ source_final ^ "·" ])
  else
    let target_name = source_prefix @ [ avoid_keywords (lexical_conventions source_final) ] in
    { env with globals = NameMap.add source_name target_name env.globals }, target_name

let push_type env x = { env with type_vars = x :: env.type_vars }

let rec push_n_type env n =
  if n = 0 then
    env
  else
    push_n_type (push_type env ("T" ^ string_of_int n)) (n - 1)

let lookup env x =
  try
    List.nth env.vars x
  with Failure _ ->
    if env.debug then
      `Named ("@" ^ string_of_int x)
    else
      Warn.fatal_error "internal error: unbound variable %d" x

let lookup_type env x =
  List.nth env.type_vars x

let fresh prefix = { vars = []; prefix; debug = false; type_vars = []; globals = NameMap.empty }

let debug = { vars = []; prefix = []; debug = true; type_vars = []; globals = NameMap.empty }

let print env =
  print_endline (String.concat ", " (List.map (function
    | `Named x -> x
    | `GoneUnit -> "–"
  ) env.vars))

let is_uppercase c =
  'A' <= c && c <= 'Z'

let print_name env n =
  let n = try NameMap.find n env.globals with Not_found -> n in
  let n =
    if List.length n > List.length env.prefix && fst (KList.split (List.length env.prefix) n) = env.prefix then
      snd (KList.split (List.length env.prefix) n)
    else if is_uppercase (List.hd n).[0] || List.hd n = "krml" then
      (* TODO: uppercase means it's a reference to Rust stdlib and outside the
         crate, therefore doesn't need the crate:: prefix *)
      n
    else
      (* Absolute reference, restart from crate top *)
      "crate" :: n
  in
  group (separate_map (colon ^^ colon) string n)

let print_path _env n =
  group (separate_map dot string n)

let string_of_width (w: Constant.width) =
  match w with
  | Constant.UInt8 -> "u8"
  | Constant.UInt16 -> "u16"
  | Constant.UInt32 -> "u32"
  | Constant.UInt64 -> "u64"
  | Constant.Int8 -> "i8"
  | Constant.Int16 -> "i16"
  | Constant.Int32 -> "i32"
  | Constant.Int64 -> "i64"
  | Constant.Bool -> "bool"
  | Constant.SizeT -> "usize"
  | Constant.CInt -> ""
  | Constant.PtrdiffT -> failwith "unexpected: ptrdifft"

let print_borrow_kind k =
  match k with
  | Mut -> string "mut" ^^ break1
  | Shared -> empty

let print_constant (w, s) =
  if w <> Constant.Bool then
    string s ^^ string (string_of_width w)
  else
    string s

let print_lifetime = function
  | Label l ->
      squote ^^ string l

let print_lifetime_option = function
  | Some l ->
      print_lifetime l ^^ space
  | None ->
      empty

let rec print_typ env (t: typ): document =
  match t with
  | Constant w -> string (string_of_width w)
  | Ref (lt, k, t) -> group (ampersand ^^ print_lifetime_option lt ^^ print_borrow_kind k ^^ print_typ env t)
  | Vec t -> group (string "Vec" ^^ angles (print_typ env t))
  | Array (t, n) -> group (brackets (print_typ env t ^^ semi ^/^ int n))
  | Slice t -> group (brackets (print_typ env t))
  | Unit -> parens empty
  | Function (n, ts, t) ->
      let env = push_n_type env n in
      group @@
      group (parens (separate_map (comma ^^ break1) (print_typ env) ts)) ^/^
      print_typ env t
  | Bound n ->
      begin try
        string (lookup_type env n)
      with _ ->
        bang ^^ bang ^^ int n
      end
  | Name (n, params) ->
      print_name env n ^^ print_generic_params params
  | Tuple ts ->
      group (parens (separate_map (comma ^^ break1) (print_typ env) ts))
  | App (t, ts) ->
      group (print_typ env t ^^
        angles (separate_map (comma ^^ break1) (print_typ env) ts))

and print_generic_params params =
  if params = [] then
    empty
  else
    break1 ^^ angles (separate_map (comma ^^ break1) (function
      | Lifetime l -> print_lifetime l
    ) params)

let print_mut b =
  if b then string "mut" ^^ break1 else empty

let print_binding env { mut; name; typ } =
  group (print_mut mut ^^ string name ^^ colon ^/^ print_typ env typ)

let print_op = function
  | Constant.BNot -> string "!"
  | op -> print_op op

(* print a block *and* the expression within it *)
let rec print_block_expression env e =
  braces_with_nesting (print_statements env e)

and print_block_or_if_expression env e =
  match e with
  | IfThenElse _ -> print_expr env max_int e
  | _ -> print_block_expression env e

(* print an expression that possibly already has a block structure... quite
   confusing, but that's the terminology used by the rust reference *)
and print_expression_with_block env (e: expr): document =
  if is_expression_with_block e then
    print_expr env max_int e
  else
    print_block_expression env e

and print_statements env (e: expr): document =
  match e with
  | Let ({ typ = Unit; _ }, Unit, e2) ->
      (* Special-case: if we have a unit (probably due to an erased node), we omit it.
         Note, there already is a similar pass (Simplify.let_to_sequence) operating
         on Ast, however, the Ast to MiniRust translation reintroduces unit statements,
         e.g., when erasing push/pop_frame or free nodes. We thus need an additional
         handling here *)
      print_statements (push env (`GoneUnit)) e2
  | Let ({ typ = Unit; _ }, e1, e2) ->
      print_expr env max_int e1 ^^ semi ^^ hardline ^^
      print_statements (push env (`GoneUnit)) e2
  | Let ({ name; _ } as b, e1, e2) ->
      let name = allocate_name env name in
      let b = { b with name } in
      group (
        group (string "let" ^/^ print_binding env b ^/^ equals) ^^
        nest 4 (break 1 ^^ print_expr env max_int e1) ^^ semi) ^^ hardline ^^
      print_statements (push env (`Named name)) e2
  | _ ->
      print_expr env max_int e

(*

The precedence of Rust operators and expressions is ordered as follows, going
from strong to weak. Binary Operators at the same precedence level are grouped
in the order given by their associativity.

Level	Operator/Expression		Associativity
=====	===================		=============
 1	Paths
 2	Method calls
 3	Field expression		left to right
 4	Function calls, array indexing
 5	?
 6	Unary - * ! & &mut
 7	as				left to right
 8	* / %				left to right
 9	+ -				left to right
10	<< >>				left to right
11	&				left to right
12	^				left to right
13	|				left to right
14	== != < > <= >=			Require parentheses
15	&&				left to right
16	||				left to right
17	.. ..=				Require parentheses
18	= += -= *= /= %=
  	&= |= ^= <<= >>=		right to left
19	return break closures

*)

(* See PrintC for the original inspiration. We return <ours>, <left>, <right> *)
and prec_of_op2 o =
  let open Constant in
  match o with
  | Mult | Div | Mod -> 8, 8, 7
  | Add | Sub -> 9, 9, 8
  | BShiftL | BShiftR -> 10, 10, 9
  | BAnd -> 11, 11, 10
  | BXor -> 12, 12, 11
  | BOr -> 13, 13, 12
  | Eq | Neq | Lt | Gt | Lte | Gte -> 14, 13, 13
  | And -> 15, 15, 14
  | Or -> 16, 16, 15
  | _ -> failwith ("unexpected: unknown binary operator: " ^ Constant.show_op o)

and prec_of_op1 o =
  let open Constant in
  match o with
  | Not | BNot | Neg -> 6
  | _ -> failwith "unexpected: unknown unary operator"


and print_expr env (context: int) (e: expr): document =
  (* If the current expressions precedence level exceeds that of the context, it
     needs to be parenthesized, otherwise it'll parse incorrectly. *)
  let paren_if mine doc =
    if mine > context then
      parens doc
    else
      doc
  in
  let print_call env e ts es =
    let mine = 4 in
    let tapp =
      if ts = [] then
        empty
      else
        colon ^^ colon ^^ angles (separate_map (comma ^^ break1) (print_typ env) ts)
    in
    paren_if mine @@
    group (print_expr env mine e ^^ tapp ^^ parens_with_nesting (
      separate_map (comma ^^ break1) (print_expr env max_int) es))
  in
  match e with
  | Operator _ ->
      failwith "unexpected: standalone operator"
  | Array e ->
      print_array_expr env e
  | VecNew e ->
      group (string "vec!" ^^ print_array_expr env e)
  | Name n ->
      print_name env n
  | Borrow (k, e) ->
      let mine = 6 in
      paren_if mine @@
      group (ampersand ^^ print_borrow_kind k ^^ print_expr env mine e)
  | Constant c ->
      print_constant c
  | Let _ ->
      print_block_expression env e
  | Call (Operator o, ts, [ e1; e2 ]) ->
      assert (ts = []);
      let mine, left, right = prec_of_op2 o in
      paren_if mine @@
      group (print_expr env left e1 ^/^
        (nest 4 (print_op o) ^/^ print_expr env right e2))
  | Call (Operator o, ts, [ e1 ]) ->
      assert (ts = []);
      let mine = prec_of_op1 o in
      paren_if mine @@
      group (print_op o ^/^ print_expr env mine e1)
  | Call (Name ["krml"; "unroll_for!"] as e, [], [ e1; ConstantString i; e3; e4; e5 ]) ->
      (* This works because the variable only appears in the body, other
         arguments are constants. *)
      let i = allocate_name env i in
      print_call (push env (`Named i)) e [] [ e1; ConstantString i; e3; e4; e5 ]
  | Call (e, ts, es) ->
      print_call env e ts es
  | Unit ->
      lparen ^^ rparen
  | Panic msg ->
      group (string "panic!" ^^ parens_with_nesting (dquotes (string msg)))
  | IfThenElse (e1, e2, e3) ->
      group @@
      group (string "if" ^/^ print_expr env max_int e1) ^/^
      print_block_expression env e2 ^^
      begin match e3 with
      | Some e3 ->
          break1 ^^ string "else" ^/^ print_block_or_if_expression env e3
      | None ->
          empty
      end
  | Assign (e1, e2, _) ->
      let mine, left, right = 18, 17, 18 in
      paren_if mine @@
      group (print_expr env left e1 ^^ space ^^ equals ^^
        (nest 4 (break1 ^^ print_expr env right e2)))
  | AssignOp (e1, o, e2, _) ->
      let mine, left, right = 18, 17, 18 in
      paren_if mine @@
      group (print_expr env left e1 ^^ space ^^ print_op o ^^ equals ^^
        (nest 4 (break1 ^^ print_expr env right e2)))
  | As (e1, e2) ->
      let mine = 7 in
      paren_if mine @@
      group (print_expr env mine e1 ^/^ string "as" ^/^ print_typ env e2)
  | For (b, e1, e2) ->
      let name = allocate_name env b.name in
      group @@
      (* Note: specifying the type of a pattern isn't supported, per rustc *)
      group (string "for" ^/^ string name ^/^ string "in" ^/^ print_expr env max_int e1) ^/^
      let env = push env (`Named name) in
      print_block_expression env e2
  | While (e1, e2) ->
      group @@
      string "while" ^/^ print_expr env max_int e1 ^/^
      print_expression_with_block env e2
  | MethodCall (e, path, es) ->
      let mine = 2 in
      paren_if mine @@
      group (print_expr env mine e ^^ dot ^^ print_path env path ^^ parens_with_nesting (
        separate_map (comma ^^ break1) (print_expr env max_int) es))
  | Range (e1, e2, inclusive) ->
      let mine = 17 in
      let module Option = Stdlib.Option in
      paren_if mine @@
      let e1 = Option.value ~default:empty (Option.map (print_expr env mine) e1) in
      let e2 = Option.value ~default:empty (Option.map (print_expr env mine) e2) in
      let inclusive = if inclusive then equals else empty in
      e1 ^^ dot ^^ dot ^^ e2 ^^ inclusive
  | ConstantString s ->
      dquotes (string (CStarToC11.escape_string s))

  | Struct (cons, fields) ->
      group @@
      print_name env cons ^/^ braces_with_nesting (
        separate_map (comma ^^ break1) (fun (f, e) ->
          group @@
          if string f = print_expr env max_int e then
            (* If the field name is the same as the expression assigned to it
               (typically, a variable name), we do not need to duplicate it *)
            string f
          else
            string f ^^ colon ^/^ group (print_expr env max_int e)
        ) fields
      )

  | Var v ->
      begin match lookup env v with
      | `Named x -> string x
      | `GoneUnit -> print env; failwith "unexpected: unit-returning computation was let-bound and used"
      end

  | Index (p, e) ->
      let mine = 4 in
      paren_if mine @@
      print_expr env mine p ^^ group (brackets (print_expr env max_int e))
  | Field (e, s, _) ->
      group (print_expr env 3 e ^^ dot ^^ string s)
  | Deref e ->
      let mine = 6 in
      paren_if mine @@
      group (star ^^ print_expr env mine e)

  | Match (scrut, patexprs) ->
      group @@
      group (string "match" ^/^ print_expr env max_int scrut) ^/^ braces_with_nesting (
        separate_map (comma ^^ break1) (fun (p, e) ->
          group @@
          group (print_pat env p ^/^ string "=>") ^^ group (nest 2 (break1 ^^ print_expr env max_int e))
      ) patexprs)

  | Open { name; _ } -> at ^^ string name

and print_pat env (p: pat) =
  match p with
  | Literal c -> print_constant c
  | Wildcard -> underscore
  | StructP name -> print_name env name

and print_array_expr env (e: array_expr) =
  match e with
  | List es ->
      group @@
      brackets (nest 4 (flow_map (comma ^^ break1) (print_expr env max_int) es))
  | Repeat (e, n) ->
      group @@
      group (brackets (nest 4 (print_expr env max_int e ^^ semi ^/^ print_expr env max_int n)))

let arrow = string "->"

let print_visibility v =
  match v with
  | None -> empty
  | Some Pub -> string "pub" ^^ break1
  | Some PubCrate -> string "pub(crate)" ^^ break1

let print_inline_and_meta inline { visibility; comment } =
  let inline = if inline then string "#[inline]" ^^ break1 else empty in
  let comment =
    if comment <> "" then
      string "/**" ^^ hardline ^^ string (String.trim comment) ^^ hardline ^^ string "*/" ^^ hardline
    else empty
  in
  comment ^^ group (inline ^^ print_visibility visibility)

let print_meta = print_inline_and_meta false

let rec print_decl env (d: decl) =
  let env, target_name = register_global env (name_of_decl d) in
  env, match d with
  | Function { type_parameters; parameters; return_type; body; meta; inline; _ } ->
      assert (type_parameters = 0);
      let parameters = List.map (fun (b: binding) -> { b with name = allocate_name env b.name }) parameters in
      let env = List.fold_left (fun env (b: binding) -> push env (`Named b.name)) env parameters in
      group @@
      group (group (print_inline_and_meta inline meta ^^ string "fn" ^/^ print_name env target_name) ^^
        parens_with_nesting (separate_map (comma ^^ break1) (print_binding env) parameters) ^^
        (match return_type with | Unit -> empty | _ -> space ^^ arrow ^^ (nest 4 (break1 ^^ print_typ env return_type)))) ^/^
      print_block_expression env body
  | Constant { typ; body; meta; _ } ->
      group @@
      group (print_meta meta ^^ string "const" ^/^ print_name env target_name ^^ colon ^/^ print_typ env typ ^/^ equals) ^^
      nest 4 (break1 ^^ print_expr env max_int body) ^^ semi
  | Enumeration { items; meta; derives; _ } ->
      group @@
      group (print_derives derives) ^/^
      group (print_meta meta ^^ string "enum" ^/^ print_name env target_name) ^/^
      braces_with_nesting (
        separate_map (comma ^^ hardline) (fun (item_name, item_struct) ->
          group @@
          print_name env item_name ^^ match item_struct with
          | None -> empty
          | Some item_struct -> break1 ^^ print_struct env item_struct
      ) items)
  | Struct { fields; meta; generic_params; _ } ->
      group @@
      group (print_meta meta ^^ string "struct" ^/^ print_name env target_name ^^ print_generic_params generic_params) ^/^
      braces_with_nesting (print_struct env fields)
  | Alias { generic_params; body; meta; _ } ->
      group @@
      group (print_meta meta ^^ string "type" ^/^ print_name env target_name  ^^ print_generic_params generic_params ^/^ equals) ^/^
      group (print_typ env body ^^ semi)

and print_derives traits =
  group @@
  string "#[derive(" ^^
  separate_map (comma ^^ break1) (function
    | PartialEq -> string "PartialEq"
    | Clone -> string "Clone"
    | Copy -> string "Copy"
  ) traits ^^
  string ")]"

and print_struct env fields =
  separate_map (comma ^^ break1) (fun { name; typ; visibility } ->
    group (group (print_visibility visibility ^^ string name ^^ colon) ^/^ group (print_typ env typ))
  ) fields

let failures = ref 0

let string_of_name = String.concat "::"

let print_decl env d =
  try
    print_decl env d
  with e ->
    incr failures;
    KPrint.bprintf "%sERROR printing %s: %s%s\n%s\n" Ansi.red
      (string_of_name (name_of_decl d))
      (Printexc.to_string e) Ansi.reset
      (Printexc.get_backtrace ());
    env, empty

let print_decls ns ds =
  let env = fresh ns in
  let env, ds = List.fold_left (fun (env, ds) d ->
    let env, d = print_decl env d in
    env, d :: ds
  ) (env, []) ds in
  let ds = List.rev ds in
  if Options.debug "rs-names" then
    NameMap.iter (fun source target ->
      KPrint.bprintf "%s --> %s\n" (String.concat "," source) (String.concat "," target)
    ) env.globals;
  separate (hardline ^^ hardline) ds ^^ hardline

let pexpr = printf_of_pprint (print_expr debug max_int)
let ptyp = printf_of_pprint (print_typ debug)
let pdecl = printf_of_pprint (fun x -> snd (print_decl debug x))

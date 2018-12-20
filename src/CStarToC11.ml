(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 License. *)

(** Converting from C* to C abstract syntax. *)

module C = C11

open C
open CStar
open KPrint
open Common

let zero = C.Constant (K.UInt8, "0")

let is_array = function Array _ -> true | _ -> false

let fresh =
  let r = ref (-1) in
  fun () ->
    incr r;
    "_" ^ string_of_int !r

let escape_string s =
  let b = Buffer.create 256 in
  String.iter (fun c ->
    match c with
    | '\x27' -> Buffer.add_string b "\\'"
    | '\x22' -> Buffer.add_string b "\\\""
    | '\x3f' -> Buffer.add_string b "\\?"
    | '\x5c' -> Buffer.add_string b "\\\\"
    | '\x07' -> Buffer.add_string b "\\a"
    | '\x08' -> Buffer.add_string b "\\b"
    | '\x0c' -> Buffer.add_string b "\\f"
    | '\x0a' -> Buffer.add_string b "\\n"
    | '\x0d' -> Buffer.add_string b "\\r"
    | '\x09' -> Buffer.add_string b "\\t"
    | '\x0b' -> Buffer.add_string b "\\v"
    | '\x20'..'\x7e' -> Buffer.add_char b c
    | _ -> Printf.bprintf b "\\x%02x" (Char.code c)
  ) s;
  Buffer.contents b

let assert_var =
  function
  | Var v | Qualified v -> v
  | e -> Warnings.fatal_error
      "TODO: for (int i = 0, t tmp = e1; i < ...; ++i) tmp[i] = \n%s is not a var"
      (show_expr e)

module S = Set.Make(String)

let rec vars_of = function
  | CStar.Var v
  | CStar.Qualified v ->
      S.singleton v
  | CStar.Constant _
  | CStar.Bool _
  | CStar.StringLiteral _
  | CStar.Any
  | CStar.EAbort _
  | CStar.Op _ ->
      S.empty
  | CStar.Cast (e, _)
  | CStar.Field (e, _)
  | CStar.AddrOf e
  | CStar.InlineComment (_, e, _) ->
      vars_of e
  | CStar.BufRead (e1, e2)
  | CStar.BufSub (e1, e2)
  | CStar.Comma (e1, e2)
  | CStar.BufCreate (_, e1, e2) ->
      S.union (vars_of e1) (vars_of e2)
  | CStar.Call (e, es) ->
      List.fold_left S.union (vars_of e) (List.map vars_of es)
  | CStar.BufCreateL (_, es) ->
      KList.reduce S.union (List.map vars_of es)
  | CStar.Struct (_, fieldexprs) ->
      KList.reduce S.union (List.map (fun (_, e) -> vars_of e) fieldexprs)

let c99_format w =
  let open K in
  "PRIx" ^ string_of_int (bytes_of_width w * 8)

let mk_debug name parameters =
  if Options.debug "c-calls" then
    let formats, args = List.split (List.map (fun (name, typ) ->
      match typ with
      | Int w ->
          Printf.sprintf "%s=0x%%08\"%s\"" name (c99_format w), C.Name name
      | Bool ->
          Printf.sprintf "%s=%%d" name, C.Name name
      (* | Pointer (Int w) -> *)
      (*     Some (Printf.sprintf "%s[0]=%%\"%s\"" name (c99_format w), C.Deref (C.Name name)) *)
      | _ ->
          Printf.sprintf "%s=%%s" name, C.Literal "unknown"
    ) parameters) in
    [ C.Expr (C.Call (C.Name "KRML_HOST_PRINTF", [
        C.Literal (String.concat " " (name :: formats @ [ "\\n" ]))
      ] @ args)) ]
  else
    []

let mk_pretty_type = function
  | "FStar_UInt128_uint128" when !Options.builtin_uint128 ->
      "uint128_t"
  | x ->
      x

(* Turns the ML declaration inside-out to match the C reading of a type.
 *   See: en.cppreference.com/w/c/language/declarations.
 * The continuation is key in the Function case. *)
let rec mk_spec_and_decl name qs (t: typ) (k: C.declarator -> C.declarator):
  C.qualifier list * C.type_spec * C.declarator
=
  match t with
  | Const t ->
      mk_spec_and_decl name [ C.Const ] t k
  | Pointer t ->
      mk_spec_and_decl name [] t (fun d -> Pointer (qs, k d))
  | Array (t, size) ->
      (* F* guarantees that the initial size of arrays is always something
       * reasonable (i.e. <4GB). *)
      let size = match size with
        | Constant k -> C.Constant k
        | _ -> mk_expr size
      in
      mk_spec_and_decl name [] t (fun d -> Array (qs, k d, size))
  | Function (cc, t, ts) ->
      (* Function types are pointers to function types, except in the top-level
       * declarator for a function, which gets special treatment via
       * mk_spec_and_declarator_f. *)
      mk_spec_and_decl name [] t (fun d ->
        Function (cc, Pointer (qs, k d), List.mapi (fun i t ->
          mk_spec_and_decl (KPrint.bsprintf "x%d" i) [] t (fun d -> d)) ts))
  | Int w ->
      qs, Int w, k (Ident name)
  | Void ->
      qs, Void, k (Ident name)
  | Qualified l ->
      qs, Named (mk_pretty_type l), k (Ident name)
  | Enum tags ->
      qs, Enum (None, tags), k (Ident name)
  | Bool ->
      qs, Named "bool", k (Ident name)
  | Struct fields ->
      qs, Struct (None, mk_fields fields), k (Ident name)
  | Union fields ->
      qs, Union (None, List.map (fun (name, typ) ->
        let qs, spec, decl = mk_spec_and_decl name [] typ (fun d -> d) in
        qs, spec, None, [ decl, None ]
      ) fields), k (Ident name)

and mk_fields fields =
  Some (List.map (fun (name, typ) ->
    let name = match name with Some name -> name | None -> "" in
    let qs, spec, decl = mk_spec_and_declarator name typ in
    qs, spec, None, [ decl, None ]
  ) fields)

(* Standard spec/declarator pair (e.g. int x). *)
and mk_spec_and_declarator name t =
  mk_spec_and_decl name [] t (fun d -> d)

(* A variant dedicated to typedef's, where we need to name structs. *)
and mk_spec_and_declarator_t name t =
  match t with
  | Struct fields ->
      (* In C, there's a separate namespace for struct names; our type names are
       * unique, therefore, post-fixing them with "_s" also generates a set of
       * unique struct names. *)
      [], C.Struct (Some (name ^ "_s"), mk_fields fields), Ident name
  | _ ->
      mk_spec_and_declarator name t

(* A variant dedicated to functions that avoids the conversion of function type
 * to pointer-to-function. *)
and mk_spec_and_declarator_f cc name ret_t params =
  mk_spec_and_decl name [] ret_t (fun d ->
    Function (cc, d, List.map (fun (n, t) -> mk_spec_and_declarator n t) params))

(* Enforce the invariant that declarations are wrapped in compound statements
 * and cannot appear "alone". *)
and mk_compound_if (stmts: C.stmt list): C.stmt =
  match stmts with
  | [ Decl _ ] ->
      Compound stmts
  | [ stmt ] when not !Options.curly_braces ->
      stmt
  | _ ->
      Compound stmts

and ensure_compound (stmts: C.stmt list): C.stmt =
  match stmts with
  | [ Compound _ as stmt ] ->
      stmt
  | _ ->
      Compound stmts

(* Ideally, most of the for-loops should've been desugared C89-style if needed
 * beforehand. *)
and mk_for_loop name qs t init test incr body =
  if !Options.c89_scope then
    Compound [
      Decl (qs, t, None, [ Ident name, None ]);
      For (
        `Expr (Op2 (K.Assign, Name name, init)),
        test, incr, body)
    ]
  else
    For (
      `Decl (qs, t, None, [ Ident name, Some (InitExpr init)]),
      test, incr, body)

and mk_for_loop_initializer e_array e_size e_value: C.stmt =
  match e_size with
  | C.Constant (_, "1")
  | C.Cast (_, C.Constant (_, "1")) ->
      Expr (Op2 (K.Assign, Index (e_array, Constant (K.UInt32, "0")), e_value))
  | _ ->
      mk_for_loop "_i" [] (Int K.UInt32) zero
        (Op2 (K.Lt, Name "_i", e_size))
        (Op1 (K.PreIncr, Name "_i"))
        (Expr (Op2 (K.Assign, Index (e_array, Name "_i"), e_value)))

and mk_memset_zero_initializer e_array e_size =
  Expr (Call (Name "memset", [
    e_array;
    Constant (K.UInt8, "0");
    Op2 (K.Mult,
      e_size,
      Sizeof (Index (e_array, zero)))]))

and mk_check_size t n_elements: C.stmt list =
  (* [init] is the default value for the elements of the array, and [n_elements] is
   * hopefully a constant *)
  let default = [ C.Expr (C.Call (C.Name "KRML_CHECK_SIZE", [ mk_sizeof t; n_elements ])) ] in
  match t, n_elements with
  | Int w, C.Cast (_, C.Constant (_, n_elements)) ->
      let size_bytes = Z.(of_int (K.bytes_of_width w) * of_string n_elements) in
      (* Note: this is wrong if anyone ever decides to use the x32 ABI *)
      let ptr_size = Z.(if !Options.m32 then one lsl 32 else one lsl 64) in
      if Z.( lt size_bytes ptr_size ) then
        []
      else
        default
  | _ ->
      default

and mk_sizeof t =
  C.Sizeof (C.Type (mk_type t))

and mk_sizeof_mul t s =
  match s with
    | C.Constant (_, "1")
    | C.Cast (_, C.Constant (_, "1")) ->
        mk_sizeof t
    | _ ->
        C.Op2 (K.Mult, mk_sizeof t, s)

and mk_malloc t s =
  C.Call (C.Name "KRML_HOST_MALLOC", [ mk_sizeof_mul t s ])

and mk_calloc t s =
  C.Call (C.Name "KRML_HOST_CALLOC", [ s; mk_sizeof t ])

and mk_free e =
  C.Call (C.Name "KRML_HOST_FREE", [ e ])

and mk_eternal_bufcreate buf (t: CStar.typ) init size =
  let size = mk_expr size in
  let e, extra_stmt = match init with
    | Constant (_, "0") ->
        mk_calloc t size, []
    | Any | Cast (Any, _) ->
        mk_malloc t size, []
    | _ ->
        mk_malloc t size,
        [ mk_for_loop_initializer (mk_expr buf) size (mk_expr init) ]
  in
  mk_check_size t size, e, extra_stmt

and assert_pointer t =
  match t with
  | Array (t, _)
  | Pointer t ->
      t
  | _ ->
      Warnings.fatal_error "let-bound bufcreate has type %s instead of Pointer" (show_typ t)

and ensure_array t size =
  match t with
  | Pointer t ->
      Array (t, size)
  | Array _ as t ->
      t
  | t ->
      Warnings.fatal_error "impossible: %s" (show_typ t)

and decay_array t =
  match t with
  | Array (t, _) ->
      Pointer t
  | t ->
      Warnings.fatal_error "impossible: %s" (show_typ t)

and mk_stmt (stmt: stmt): C.stmt list =
  match stmt with
  | Comment s ->
      [ Comment s ]

  | Return e ->
      let e = Option.map (fun e ->
        let e = mk_expr e in
        if Options.debug "c-calls" then
          C.Call (Name "KRML_DEBUG_RETURN", [ e ])
        else
          e
      ) e in
      [ Return e ]

  | Block stmts ->
      [ Compound (mk_stmts stmts) ]

  | Break ->
      [ Break ]

  | Ignore e ->
      [ Expr (mk_expr e) ]

  | Decl (binder, BufCreate ((Eternal | Heap), init, size)) ->
      let t = assert_pointer binder.typ in
      let stmt_check, expr_alloc, stmt_extra =
        mk_eternal_bufcreate (Var binder.name) t init size
      in
      let qs, spec, decl = mk_spec_and_declarator binder.name binder.typ in
      let decl: C.stmt list = [ Decl (qs, spec, None, [ decl, Some (InitExpr expr_alloc)]) ] in
      stmt_check @ decl @ stmt_extra

  | Decl (binder, BufCreate (Stack, init, size)) ->
      (* In the case where this is a buffer creation in the C* meaning, then we
       * declare a fixed-length array; this is an "upcast" from pointer type to
       * array type, in the C sense. *)
      let t = ensure_array binder.typ size in
      let module T = struct type init = Nope | Memset | Forloop end in
      let is_constant = match size with Constant _ -> true | _ -> false in
      let use_alloca = not is_constant && !Options.alloca_if_vla in
      let (maybe_init, init_type): C.init option * T.init = match init, size with
        | _, Constant (_, "0") ->
            (* zero-sized array *)
            None, T.Nope
        | Cast (Any, _), _
        | Any, _ ->
            (* no initial value *)
            None, T.Nope
        | Constant ((_, "0") as k), Constant _ when not use_alloca ->
            (* The only case the we can initialize statically is a known, static
             * size _and_ a zero initializer. If we're about to alloca, don't
             * use a zero-initializer. *)
            Some (Initializer [ InitExpr (C.Constant k) ]), T.Nope
        | Constant (_, "0"), _ ->
            None, T.Memset
        | _ ->
            None, T.Forloop
      in
      let size = mk_expr size in
      let t, maybe_init =
        (* If we're doing an alloca, override the initial value (it's now the
         * call to alloca) and decay the array to a pointer type. *)
        if use_alloca then
          let bytes = C.Call (C.Name "alloca", [
            C.Op2 (K.Mult, size, C.Sizeof (C.Type (mk_type (assert_pointer t)))) ]) in
          assert (maybe_init = None);
          decay_array t, Some (InitExpr bytes)
        else
          t, maybe_init
      in
      let init = mk_expr init in
      let qs, spec, decl = mk_spec_and_declarator binder.name t in
      let extra_stmt: C.stmt list =
        match init_type with
        | T.Memset ->
            [ mk_memset_zero_initializer (Name binder.name) size ]
        | T.Nope ->
            [ ]
        | T.Forloop ->
            (* Note: only works if the length and initial value are pure
             * computations... which F* guarantees! *)
            [ mk_for_loop_initializer (Name binder.name) size init ]
      in
      let decl: C.stmt list = [ Decl (qs, spec, None, [ decl, maybe_init ]) ] in
      mk_check_size (assert_pointer binder.typ) size @
      decl @
      extra_stmt

  | Decl (_, BufCreateL ((Eternal | Heap), _)) as s ->
      failwith ("TODO: the array below is either in the eternal or heap region, \
        uses createL, but we don't have (yet) codegen for this:\n" ^
        CStar.show_stmt s)

  | Decl (binder, BufCreateL (Stack, inits)) ->
      let t = ensure_array binder.typ (Constant (K.uint32_of_int (List.length inits))) in
      let qs, spec, decl = mk_spec_and_declarator binder.name t in
      [ Decl (qs, spec, None, [ decl, Some (Initializer (List.map (fun e ->
        InitExpr (mk_expr e)
      ) inits))])]

  | Decl (binder, e) ->
      let qs, spec, decl = mk_spec_and_declarator binder.name binder.typ in
      let init: init option = match e with Any -> None | _ -> Some (struct_as_initializer e) in
      [ Decl (qs, spec, None, [ decl, init ]) ]

  | IfThenElse (e, b1, b2) ->
      if List.length b2 > 0 then
        [ IfElse (mk_expr e, mk_compound_if (mk_stmts b1), mk_compound_if (mk_stmts b2)) ]
      else
        [ If (mk_expr e, mk_compound_if (mk_stmts b1)) ]

  | Assign (BufRead _, _, (Any | Cast (Any, _))) ->
      []

  | Assign (e1, t, BufCreate (Eternal, init, size)) ->
      let v = assert_var e1 in
      (* Evil bug:
       *   x <- bufcreate 1 e[x]
       * might become:
       *   x <- bufcreate 1 any
       *   x[0] <- e[x]    <--- does NOT evaluate to the previous value of x
       * Note: from Simplify.ml we know that BufCreate appears only under a
       * [Decl] node or an [Assign] node. Name collisions are not possible with
       * the Decl case since [AstToCStar] would've avoided the name conflict,
       * and F* does not have recursive value definitions.
       *)
      let vs = vars_of init in
      if S.mem v vs then
        let t_elt = assert_pointer t in
        let name_init = "_init" ^ fresh () in
        let size = mk_expr size in
        let stmt_init = mk_stmt (Decl ({ name = name_init; typ = t_elt }, init)) in
        let stmt_assign = [ Expr (Assign (mk_expr e1, mk_malloc t_elt size)) ] in
        let stmt_fill = mk_for_loop_initializer (mk_expr e1) size (mk_expr (Var name_init)) in
        stmt_init @
        stmt_assign @
        [ stmt_fill ]
      else
        let stmt_check, expr_alloc, stmt_extra = mk_eternal_bufcreate e1 (assert_pointer t) init size in
        stmt_check @
        [ Expr (Assign (mk_expr e1, expr_alloc)) ] @
        stmt_extra

  | Assign (_, _, BufCreateL (Eternal, _)) ->
      failwith "TODO"

  | Assign (e1, _, e2) ->
      [ Expr (Assign (mk_expr e1, mk_expr e2)) ]

  | BufWrite (_, _, (Any | Cast (Any, _))) ->
      []

  | BufWrite (e1, e2, e3) ->
      [ Expr (Assign (mk_index e1 e2, mk_expr e3)) ]

  | BufBlit (e1, e2, e3, e4, e5) ->
      let dest = match e4 with
        | Constant (_, "0") -> mk_expr e3
        | _ -> Op2 (K.Add, mk_expr e3, mk_expr e4)
      in
      let source = match e2 with
        | Constant (_, "0") -> mk_expr e1
        | _ -> Op2 (K.Add, mk_expr e1, mk_expr e2)
      in
      [ Expr (Call (Name "memcpy", [
        dest;
        source;
        Op2 (K.Mult, mk_expr e5, Sizeof (Index (mk_expr e1, zero)))])) ]

  | BufFill (buf, v, size) ->
      (* Again, assuming that these are non-effectful. *)
      let buf = mk_expr buf in
      let v = mk_expr v in
      let size = mk_expr size in
      [ mk_for_loop_initializer buf size v ]

  | BufFree e ->
      [ Expr (mk_free (mk_expr e)) ]

  | While (e1, e2) ->
      [ While (mk_expr e1, mk_compound_if (mk_stmts e2)) ]

  | PushFrame | PopFrame ->
      failwith "[mk_stmt]: nested frames to be handled by [mk_stmts]"

  | Switch (e, branches, default) ->
      [ Switch (
          mk_expr e,
          List.map (fun (ident, block) ->
            (match ident with
            | `Ident ident -> Name ident
            | `Int k -> Constant k),
            let block = mk_stmts block in
            if List.length block > 0 then
              match KList.last block with
              | Return _ -> Compound block
              | _ -> Compound (block @ [ Break ])
            else
              Compound [ Break ]
          ) branches,
          match default with
          | Some block ->
              Compound (mk_stmts block)
          | _ ->
              Compound [
                Expr (Call (Name "KRML_HOST_PRINTF", [
                  Literal "KreMLin incomplete match at %s:%d\\n"; Name "__FILE__"; Name "__LINE__"  ]));
                Expr (Call (Name "KRML_HOST_EXIT", [ Constant (K.UInt8, "253") ]))
              ]
      )]

  | Abort s ->
      [ Expr (Call (Name "KRML_HOST_PRINTF", [
          Literal "KreMLin abort at %s:%d\\n%s\\n"; Name "__FILE__"; Name "__LINE__"; Literal (escape_string s) ]));
        Expr (Call (Name "KRML_HOST_EXIT", [ Constant (K.UInt8, "255") ])); ]

  | For (`Decl (binder, e1), e2, e3, b) ->
      let qs, spec, decl = mk_spec_and_declarator binder.name binder.typ in
      let name = match decl with Ident name -> name | _ -> failwith "not an ident" in
      let init = match struct_as_initializer e1 with InitExpr init -> init | _ -> failwith "not an initexpr" in
      let e2 = mk_expr e2 in
      let e3 = match mk_stmt e3 with [ Expr e3 ] -> e3 | _ -> assert false in
      let b = mk_compound_if (mk_stmts b) in
      [ mk_for_loop name qs spec init e2 e3 b ]

  | For (e1, e2, e3, b) ->
      let e1 = match e1 with
        | `Skip -> `Skip
        | `Stmt e1 -> `Expr (match mk_stmt e1 with [ Expr e1 ] -> e1 | _ -> assert false)
        | _ -> assert false
      in
      let e2 = mk_expr e2 in
      let e3 = match mk_stmt e3 with [ Expr e3 ] -> e3 | _ -> assert false in
      let b = mk_compound_if (mk_stmts b) in
      [ For (e1, e2, e3, b) ]


and mk_stmts stmts: C.stmt list =
  let stmts = KList.map_flatten (function
    | PushFrame | PopFrame ->
        (* We totally give up on inserting braces for push/pop frame, since
         * they're a semantic criterion in F*, which we cannot recover
         * syntactically here. See PushPop.fst in test/ for an example of a
         * tricky situation. *)
        []
    | stmt ->
        mk_stmt stmt
  ) stmts in
  let rec fixup_c89 in_decls (stmts: C.stmt list) =
    match stmts with
    | C.Decl _ as stmt :: stmts ->
        if in_decls then
          stmt :: fixup_c89 true stmts
        else
          [ C.Compound (stmt :: fixup_c89 true stmts) ]
    | stmt :: stmts ->
        stmt :: fixup_c89 false stmts
    | [] ->
        []
  in
  if !Options.c89_scope then
    fixup_c89 true stmts
  else
    stmts



and mk_index (e1: expr) (e2: expr): C.expr =
  match mk_expr e2 with
  | Cast (_, (Constant _ as c)) ->
      Index (mk_expr e1, c)
  | _ ->
      Index (mk_expr e1, mk_expr e2)

and mk_deref (e: expr) : C.expr =
  Deref (mk_expr e)

(* Some functions get a special treatment and are pretty-printed in a specific
 * way at the very last minute. KreMLin is never supposed to generate unused
 * declarations, so these primitives must not be output in the resulting C
 * files. *)
and is_primitive s =
  let known = [
    (* Useless definitions: they are bypassed by custom codegen. *)
    "LowStar_Monotonic_Buffer_is_null";
    "C_Nullity_is_null";
    "LowStar_Monotonic_Buffer_mnull";
    "LowStar_Buffer_null";
    "C_Nullity_null";
    "C_String_get";
    "C_String_t";
    "C_String_of_literal";
    "C_Compat_String_get";
    "C_Compat_String_t";
    "C_Compat_String_of_literal";
    (* Trick: we typedef this as an int and reply on implicit C enum -> int
     * conversion rules. *)
    "exit_code";
    (* These two are not integers and are macro-expanded by MingW into the
     * address of a function pointer, which would make "extern channel stdout"
     * fail. *)
    "stdout";
    "stderr";
    (* DLL linkage errors on MSVC. *)
    "rand"; "srand"; "exit"; "fflush"; "clock";
    (* Hand-written type definition parameterized over KRML_VERIFIED_UINT128 *)
    "FStar_UInt128_uint128";
    (* Macros, no external linkage *)
    "htole16";
    "le16toh";
    "htole32";
    "le32toh";
    "htole64";
    "le64toh";
    "htobe16";
    "be16toh";
    "htobe32";
    "be32toh";
    "htobe64";
    "be64toh";
    "store16_le";
    "load16_le";
    "store16_be";
    "load16_be";
    "store32_le";
    "load32_le";
    "store32_be";
    "load32_be";
    "load64_le";
    "store64_le";
    "load64_be";
    "store64_be";
  ] in
  List.mem s known ||
  KString.starts_with s "C_Nullity_op_Bang_Star__" ||
  KString.starts_with s "LowStar_BufferOps_op_Bang_Star__" ||
  KString.starts_with s "LowStar_BufferOps_op_Star_Equals__"

and mk_expr (e: expr): C.expr =
  match e with
  | InlineComment (s, e, s') ->
      InlineComment (s, mk_expr e, s')

  | Call (Op (o, _), [ e ]) ->
      Op1 (o, mk_expr e)

  | Call (Op (o, _), [ e1; e2 ]) ->
      Op2 (o, mk_expr e1, mk_expr e2)

  | Comma (e1, e2) ->
      Op2 (K.Comma, mk_expr e1, mk_expr e2)

  | Call (Qualified s, [ e1 ]) when KString.starts_with s "C_Nullity_op_Bang_Star__" ->
      mk_deref e1

  | Call (Qualified s, e1 :: _) when KString.starts_with s "LowStar_BufferOps_op_Bang_Star__" ->
      mk_deref e1

  | Call (Qualified s, e1 :: e2 :: _ ) when KString.starts_with s "LowStar_BufferOps_op_Star_Equals__" ->
      Op2 (K.Assign, mk_deref e1, mk_expr e2)

  | Call (Qualified "C_String_of_literal", [ StringLiteral _ as s ]) ->
      mk_expr s

  | Call (Qualified "C_Compat_String_of_literal", [ StringLiteral _ as s ]) ->
      mk_expr s

  | Call (Qualified "C_String_get", [ e1; e2 ])
  | Call (Qualified "C_Compat_String_get", [ e1; e2 ])
  | BufRead (e1, e2) ->
      mk_index e1 e2

  | Call (Qualified "LowStar_Monotonic_Buffer_mnull", _)
  | Call (Qualified "LowStar_Buffer_null", _)
  | Call (Qualified "C_Nullity_null", _) ->
      Name "NULL"

  | Call (Qualified "LowStar_Monotonic_Buffer_is_null", [ e ] )
  | Call (Qualified "C_Nullity_is_null", [ e ]) ->
      Op2 (K.Eq, mk_expr e, C.Name "NULL")

  | Call (Qualified "FStar_UInt128_add", [ e1; e2 ]) when !Options.builtin_uint128 ->
      Op2 (K.Add, mk_expr e1, mk_expr e2)

  | Call (Qualified "FStar_UInt128_mul", [ e1; e2 ]) when !Options.builtin_uint128 ->
      Op2 (K.Mult, mk_expr e1, mk_expr e2)

  | Call (Qualified "FStar_UInt128_add_mod", [ e1; e2 ]) when !Options.builtin_uint128 ->
      Op2 (K.Add, mk_expr e1, mk_expr e2)

  | Call (Qualified "FStar_UInt128_sub", [ e1; e2 ]) when !Options.builtin_uint128 ->
      Op2 (K.Sub, mk_expr e1, mk_expr e2)

  | Call (Qualified "FStar_UInt128_sub_mod", [ e1; e2 ]) when !Options.builtin_uint128 ->
      Op2 (K.Sub, mk_expr e1, mk_expr e2)

  | Call (Qualified "FStar_UInt128_logand", [ e1; e2 ]) when !Options.builtin_uint128 ->
      Op2 (K.BAnd, mk_expr e1, mk_expr e2)

  | Call (Qualified "FStar_UInt128_logor", [ e1; e2 ]) when !Options.builtin_uint128 ->
      Op2 (K.BOr, mk_expr e1, mk_expr e2)

  | Call (Qualified "FStar_UInt128_logxor", [ e1; e2 ]) when !Options.builtin_uint128 ->
      Op2 (K.BXor, mk_expr e1, mk_expr e2)

  | Call (Qualified "FStar_UInt128_lognot", [ e1 ]) when !Options.builtin_uint128 ->
      Op1 (K.BNot, mk_expr e1)

  | Call (Qualified "FStar_UInt128_shift_left", [ e1; e2 ]) when !Options.builtin_uint128 ->
      Op2 (K.BShiftL, mk_expr e1, mk_expr e2)

  | Call (Qualified "FStar_UInt128_shift_right", [ e1; e2 ]) when !Options.builtin_uint128 ->
      Op2 (K.BShiftR, mk_expr e1, mk_expr e2)

  | Call (Qualified "FStar_UInt128_uint64_to_uint128", [ e1 ]) when !Options.builtin_uint128 ->
      Cast (mk_type (Qualified "uint128_t"), mk_expr e1)

  | Call (Qualified "FStar_UInt128_uint128_to_uint64", [ e1 ]) when !Options.builtin_uint128 ->
      Cast (mk_type (Qualified "uint64_t"), mk_expr e1)

  | Call (Qualified "FStar_UInt128_mul_wide", [ e1; e2 ]) when !Options.builtin_uint128 ->
      Op2 (K.Mult, Cast (mk_type (Qualified "uint128_t"), mk_expr e1), mk_expr e2)

  | Call (Qualified "FStar_Int_Cast_Full_uint64_to_uint128", [ e1 ]) when !Options.builtin_uint128 ->
      Cast (mk_type (Qualified "uint128_t"), mk_expr e1)

  | Call (Qualified "FStar_Int_Cast_Full_uint128_to_uint64", [ e1 ]) when !Options.builtin_uint128 ->
      Cast (mk_type (Qualified "uint64_t"), mk_expr e1)

  | Call (e, es) ->
      Call (mk_expr e, List.map mk_expr es)

  | Var ident ->
      Name ident

  | Qualified ident ->
      Name ident

  | Constant (w, c) ->
      Cast (([], Int w, Ident ""), Constant (w, c))

  | BufCreate _ | BufCreateL _ ->
      failwith "[mk_expr]: Buffer.create; Buffer.createl may only appear as let ... = Buffer.create"

  | BufSub (e1, Constant (_, "0")) ->
      mk_expr e1

  | BufSub (e1, e2) ->
      Op2 (K.Add, mk_expr e1, mk_expr e2)

  | Cast (e, t') ->
      (* JP: what is this? TODO review. *)
      begin match e with
      | Cast (_, t) as e when t = t' || t = Int Constant.UInt8 && t' = Pointer Void ->
          mk_expr e
      | e ->
          Cast (mk_type t', mk_expr e)
      end

  | Any ->
      Cast (([], Void, Pointer ([], Ident "")), zero)

  | Op _ ->
      failwith "[mk_expr]: op should've been caught"

  | Bool b ->
      Bool b

  | Struct (typ, fields) ->
      let typ = Option.must typ in
      mk_compound_literal typ fields

  | Field (BufRead (e, Constant (_, "0")), field) ->
      MemberAccessPointer (mk_expr e, field)

  | Field (e, field) ->
      MemberAccess (mk_expr e, field)

  | StringLiteral s ->
      Literal (escape_string s)

  | AddrOf e ->
      Address (mk_expr e)

  | EAbort (t, s) ->
      Call (Name "KRML_EABORT", [ Type (mk_type t); Literal (escape_string s) ])


and mk_compound_literal name fields =
  (* TODO really properly specify C's type_name! *)
  CompoundLiteral (([], Named name, Ident ""), fields_as_initializer_list fields)

and struct_as_initializer = function
  | Struct (_, fields) ->
      Initializer (fields_as_initializer_list fields)
  | e ->
      InitExpr (mk_expr e)

and fields_as_initializer_list fields =
  List.map (function
    | Some field, e -> Designated (Dot field, struct_as_initializer e)
    | None, e -> struct_as_initializer e
  ) fields

and mk_type t =
  (* hack alert *)
  mk_spec_and_declarator "" t

let mk_comments =
  KList.filter_map (function
    | Comment c when c <> "" ->
        Some c
    | _ ->
        None
  )

let wrap_verbatim flags d =
  KList.filter_map (function
    | Prologue s -> Some (Verbatim s)
    | _ -> None
  ) flags @ [ d ] @ KList.filter_map (function
    | Epilogue s -> Some (Verbatim s)
    | _ -> None
  ) flags

let enum_as_macros cases =
  let lines: string list = List.mapi (fun i c ->
    KPrint.bsprintf "#define %s %d" c i
  ) cases in
  String.concat "\n" lines

let strengthen_array t expr =
  match expr with
  | BufCreateL (_, es) ->
      ensure_array t (Constant (K.uint32_of_int (List.length es)))
  | _ ->
      t

(** Function definition or global definition. *)
let mk_function_or_global_body (d: decl): C.declaration_or_function list =
  match d with
  | External _
  | TypeForward _
  | Type _ ->
      []

  | Function (cc, flags, return_type, name, parameters, body) ->
      if is_primitive name then
        []
      else
        begin try
          let static = if List.exists ((=) Private) flags then Some Static else None in
          let inline = List.exists ((=) Inline) flags in
          let parameters = List.map (fun { name; typ } -> name, typ) parameters in
          let qs, spec, decl = mk_spec_and_declarator_f cc name return_type parameters in
          let body = ensure_compound (mk_debug name parameters @ mk_stmts body) in
          wrap_verbatim flags (Function (mk_comments flags, inline, (qs, spec, static, [ decl, None ]), body))
        with e ->
          beprintf "Fatal exception raised in %s\n" name;
          raise e
        end

  | Global (name, flags, t, expr) ->
      if is_primitive name then
        []
      else
        let t = strengthen_array t expr in
        let qs, spec, decl = mk_spec_and_declarator name t in
        let static = if List.exists ((=) Private) flags then Some Static else None in
        match expr with
        | Any ->
            wrap_verbatim flags (Decl ([], (qs, spec, static, [ decl, None ])))
        | BufCreateL (_, es) ->
            let es = List.map struct_as_initializer es in
            wrap_verbatim flags (Decl ([], (qs, spec, static, [
              decl, Some (Initializer es) ])))
        | _ ->
            let expr = struct_as_initializer expr in
            wrap_verbatim flags (Decl ([], (qs, spec, static, [ decl, Some expr ])))

(** Function prototype, or extern global declaration (no definition). *)
let mk_function_or_global_stub (d: decl): C.declaration_or_function list =
  match d with
  | External _
  | TypeForward _
  | Type _ ->
      []

  | Function (cc, flags, return_type, name, parameters, _) ->
      if is_primitive name then
        []
      else
        begin try
          let parameters = List.map (fun { name; typ } -> name, typ) parameters in
          let qs, spec, decl = mk_spec_and_declarator_f cc name return_type parameters in
          wrap_verbatim flags (Decl (mk_comments flags, (qs, spec, None, [ decl, None ])))
        with e ->
          beprintf "Fatal exception raised in %s\n" name;
          raise e
        end

  | Global (name, flags, t, expr) ->
      if is_primitive name then
        []
      else
        let t = strengthen_array t expr in
        let qs, spec, decl = mk_spec_and_declarator name t in
        wrap_verbatim flags (Decl ([], (qs, spec, Some Extern, [ decl, None ])))

type where = H | C

(* Type declarations, external function declarations. These are the things that
 * are either declared in the header (public), or in the c file (private), but
 * not twice. *)
let mk_type_or_external (w: where) (d: decl): C.declaration_or_function list =
  let mk_forward_decl name flags =
    wrap_verbatim flags (Decl ([], ([], C.Struct (Some (name ^ "_s"), None), Some Typedef, [ Ident name, None ])))
  in
  match d with
  | TypeForward (name, flags) ->
      mk_forward_decl name flags
  | Type (name, Struct _, flags) when w = H && List.mem AbstractStruct flags ->
      mk_forward_decl name flags
  | Type (name, t, flags) ->
      if is_primitive name then
        []
      else begin
        match t with
        | Enum cases when !Options.short_enums ->
            (* Note: EEnum translates as just a name -- so we don't have to
             * change use-sites, they directly resolve as the macro. *)
            let t =
              if List.length cases <= 0xff then
                K.UInt8
              else if List.length cases <= 0xffff then
                K.UInt16
              else
                failwith (KPrint.bsprintf "Too many cases for enum %s" name)
            in
            wrap_verbatim flags (Verbatim (enum_as_macros cases)) @
            let qs, spec, decl = mk_spec_and_declarator_t name (Int t) in
            [ Decl ([], (qs, spec, Some Typedef, [ decl, None ]))]
        | _ ->
            let qs, spec, decl = mk_spec_and_declarator_t name t in
            wrap_verbatim flags (Decl ([], (qs, spec, Some Typedef, [ decl, None ])))
      end

  | External (name, Function (cc, t, ts), flags) ->
      if is_primitive name then
        []
      else
        let qs, spec, decl = mk_spec_and_declarator_f cc name t (List.mapi (fun i t ->
          KPrint.bsprintf "x%d" i, t
        ) ts) in
        wrap_verbatim flags (Decl ([], (qs, spec, Some Extern, [ decl, None ])))

  | External (name, t, flags) ->
      if is_primitive name then
        []
      else
        let qs, spec, decl = mk_spec_and_declarator name t in
        wrap_verbatim flags (Decl ([], (qs, spec, Some Extern, [ decl, None ])))

  | Function _ | Global _ ->
      []


let is_static_header name =
  List.exists (fun m -> Idents.fstar_name_of_mod m = name) !Options.static_header

let either f1 f2 x =
  match f1 x with
  | [] -> f2 x
  | l -> l

let flags_of_decl (d: CStar.decl) =
  match d with
  | Global (_, flags, _, _)
  | Function (_, flags, _, _, _, _)
  | Type (_, _, flags)
  | TypeForward (_, flags)
  | External (_, _, flags) ->
      flags

let if_private_or_abstract f d =
  let flags = flags_of_decl d in
  if List.mem Private flags || List.mem AbstractStruct flags then
    f d
  else
    []

let if_not_private f d =
  if not (List.mem Private (flags_of_decl d)) then
    f d
  else
    []

(* Building a .c file *)
let mk_files files =
  let mk_c_file decls =
    (* In the C file, we put function bodies, global bodies, and type
     * definitions and external definitions that were private to the file only.
     * *)
    KList.map_flatten
      (either mk_function_or_global_body (if_private_or_abstract (mk_type_or_external C)))
      decls
  in
  let files = List.filter (fun (name, _) -> not (is_static_header name)) files in
  List.map (fun (name, program) -> name, mk_c_file program) files

(* Building the two flavors of headers. *)
let mk_header decls =
  (* In the header file, we put functions and global stubs, along with type
   * definitions that are visible from the outside. *)
  KList.map_flatten
    (if_not_private (either mk_function_or_global_stub (mk_type_or_external H)))
    decls

let mk_static_header decls =
  let mk_static (d: C.declaration_or_function) =
    match d with
    | Decl (comments, (qs, ts, None, decl_inits)) ->
        C.Decl (comments, (qs, ts, Some Static, decl_inits))
    | Function (comments, _inline, (qs, ts, (None | Some Static), decl_inits), body) ->
        C.Function (comments, true, (qs, ts, Some Static, decl_inits), body)
    | d ->
        d
  in
  (* What should be the behavior for a type declaration marked as CAbstract but
   * whose module has -static-header? This ignores CAbstract. *)
  let decls = KList.map_flatten (either mk_function_or_global_body (mk_type_or_external C)) decls in
  List.map mk_static decls

let mk_headers files =
  List.map (fun (name, program) ->
    if is_static_header name then
      name, mk_static_header program
    else
      name, mk_header program
  ) files

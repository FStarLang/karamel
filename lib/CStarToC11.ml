(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 License. *)

(** Converting from C* to C abstract syntax. *)

module C = C11

open C
open CStar
open KPrint
open Common

let is_primitive = Helpers.is_primitive

let zero = C.Constant (K.UInt8, "0")

let is_array = function Array _ -> true | _ -> false
let is_var = function Var _ -> true | _ -> false
let is_call = function
  | Call (Qualified (_, s), _) ->
      not (KString.starts_with s "op_Bang_Star__")
  | _ -> false

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

let to_c_name = GlobalNames.to_c_name

let assert_var m =
  function
  | Var v ->
      v
  | Qualified v ->
      to_c_name m v
  | e -> Warn.fatal_error
      "TODO: for (int i = 0, t tmp = e1; i < ...; ++i) tmp[i] = \n%s is not a var"
      (show_expr e)

module S = Set.Make(String)

let rec vars_of m = function
  | CStar.Var v ->
      S.singleton v
  | Qualified v
  | Macro v ->
      S.singleton (to_c_name m v)
  | Constant _
  | Bool _
  | StringLiteral _
  | Any
  | EAbort _
  | Type _
  | BufNull
  | Op _ ->
      S.empty
  | Cast (e, _)
  | Field (e, _)
  | AddrOf e
  | InlineComment (_, e, _) ->
      vars_of m e
  | BufRead (e1, e2)
  | BufSub (e1, e2)
  | Comma (e1, e2)
  | BufCreate (_, e1, e2) ->
      S.union (vars_of m e1) (vars_of m e2)
  | Call (e, es) ->
      List.fold_left S.union (vars_of m e) (List.map (vars_of m) es)
  | BufCreateL (_, es) ->
      KList.reduce S.union (List.map (vars_of m) es)
  | Struct (_, fieldexprs) ->
      KList.reduce S.union (List.map (fun (_, e) -> vars_of m e) fieldexprs)
  | Stmt stmts ->
      vars_of_block m stmts

and vars_of_block m stmts =
  KList.reduce S.union (List.map (vars_of_stmt m) stmts)

and vars_of_stmt m = function
  | CStar.Abort _
  | Return _
  | Break
  | Continue
  | Comment _ ->
      S.empty
  | Ignore e
  | BufFree (_, e) ->
      vars_of m e
  | Block stmts ->
      vars_of_block m stmts
  | Decl ({ name; _ }, e) ->
      S.remove name (vars_of m e)
  | IfThenElse (_, e, b1, b2) ->
      S.union (vars_of m e) (S.union (vars_of_block m b1) (vars_of_block m b2))
  | While (e, b) ->
      S.union (vars_of m e) (vars_of_block m b)
  | For (i, e, s, b) ->
      begin match i with
      | `Decl ({ name; _ }, e') ->
          S.remove name (
            KList.reduce S.union [
              vars_of m e;
              vars_of m e';
              vars_of_stmt m s;
              vars_of_block m b
            ]
          )
      | `Skip ->
          KList.reduce S.union [
            vars_of m e;
            vars_of_stmt m s;
            vars_of_block m b
          ]
      | `Stmt s' ->
          KList.reduce S.union [
            vars_of m e;
            vars_of_stmt m s;
            vars_of_stmt m s';
            vars_of_block m b
          ]
      end
  | Assign (e, _, e') ->
      S.union (vars_of m e) (vars_of m e')
  | Switch (e, cs, b) ->
      KList.reduce S.union ([
        vars_of m e;
        match b with Some b -> vars_of_block m b | None -> S.empty
      ] @ List.map (fun (_, b) -> vars_of_block m b) cs)
  | BufWrite (e1, e2, e3) ->
      KList.reduce S.union [
        vars_of m e1;
        vars_of m e2;
        vars_of m e3;
      ]
  | BufFill (_, e2, e3, e4) ->
      KList.reduce S.union [
        vars_of m e2;
        vars_of m e3;
        vars_of m e4;
      ]
  | BufBlit (_, e2, e3, e4, e5, e6) ->
      KList.reduce S.union [
        vars_of m e2;
        vars_of m e3;
        vars_of m e4;
        vars_of m e5;
        vars_of m e6;
      ]

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

let bytes_in = function
  (* SizeT does not have a statically known size *)
  | Int SizeT -> None
  | Int w -> Some (K.bytes_of_width w)
  | Qualified ([ "FStar"; "UInt128" ], "uint128") -> Some (128 / 8)
  | Qualified ([ "Lib"; "IntVector"; "Intrinsics" ], "vec128") -> Some (128 / 8)
  | Qualified ([ "Lib"; "IntVector"; "Intrinsics" ], "vec256") -> Some (256 / 8)
  | Qualified ([ "Lib"; "IntVector"; "Intrinsics" ], "vec32") -> Some (32 / 8)
  | _ -> None

(* Trim all trailing zeroes from an initializer list (per the C standard, static
 * initializers guarantee for missing fields that they're initialized as if they
 * had static storage duration, i.e. with zero.). For prettyness, leave at least
 * one zero, unless the array was empty to start with (admissible with globals). *)
let trim_trailing_zeros l =
  let rec trim_trailing_zeros = function
    | CStar.Constant (_, "0") :: tl -> trim_trailing_zeros tl
    | [] -> [ CStar.Constant (K.UInt32, "0") ]
    | l -> List.rev l
  in
  match l with
  | [] -> []
  | _ -> trim_trailing_zeros (List.rev l)

(* Turns the ML declaration inside-out to match the C reading of a type.
 *   See: en.cppreference.com/w/c/language/declarations.
 * The continuation is key in the Function case. *)
let rec mk_spec_and_decl m name qs (t: typ) (k: C.declarator -> C.declarator):
  C.qualifier list * C.type_spec * C.declarator
=
  match t with
  | Const t ->
      mk_spec_and_decl m name [ C.Const ] t k
  | Pointer t ->
      mk_spec_and_decl m name [] t (fun d -> Pointer (qs, k d))
  | Array (t, size) ->
      (* F* guarantees that the initial size of arrays is always something
       * reasonable (i.e. <4GB). *)
      let size = match size with
        | Constant k -> C.Constant k
        | _ -> mk_expr m size
      in
      mk_spec_and_decl m name [] t (fun d -> Array (qs, k d, size))
  | Function (cc, t, ts) ->
      (* Function types are pointers to function types, except in the top-level
       * declarator for a function, which gets special treatment via
       * mk_spec_and_declarator_f. *)
      mk_spec_and_decl m name [] t (fun d ->
        Function (cc, Pointer (qs, k d), List.mapi (fun i t ->
          mk_spec_and_decl m (KPrint.bsprintf "x%d" i) [] t (fun d -> d)) ts))
  | Int w ->
      qs, Int w, k (Ident name)
  | Void ->
      qs, Void, k (Ident name)
  | Qualified l ->
      qs, Named (mk_pretty_type (to_c_name ~kind:Type m l)), k (Ident name)
  | Enum tags ->
      let tags = List.map (to_c_name m) tags in
      qs, Enum (None, tags), k (Ident name)
  | Bool ->
      let bool = if !Options.microsoft then "BOOLEAN" else "bool" in
      qs, Named bool, k (Ident name)
  | Struct fields ->
      qs, Struct (None, mk_fields m fields), k (Ident name)
  | Union fields ->
      qs, Union (None, mk_union_fields m fields), k (Ident name)

and mk_fields m fields =
  Some (List.map (fun (name, typ) ->
    let name = match name with Some name -> name | None -> "" in
    let qs, spec, decl = mk_spec_and_declarator m name typ in
    qs, spec, None, None, { maybe_unused = false }, [ decl, None, None ]
  ) fields)

and mk_union_fields m fields =
  Some (List.map (fun (name, typ) ->
    let qs, spec, decl = mk_spec_and_decl m name [] typ (fun d -> d) in
    qs, spec, None, None, { maybe_unused = false }, [ decl, None, None ]
  ) fields)

(* Standard spec/declarator pair (e.g. int x). *)
and mk_spec_and_declarator m name t =
  mk_spec_and_decl m name [] t (fun d -> d)

(* A variant dedicated to typedef's, where we need to name structs. *)
and mk_spec_and_declarator_t m name t =
  match t with
  | Struct fields ->
      (* In C, there's a separate namespace for struct names; our type names are
       * unique, therefore, post-fixing them with "_s" also generates a set of
       * unique struct names. *)
      [], C.Struct (Some (name ^ "_s"), mk_fields m fields), Ident name
  | Union fields ->
      [], C.Union (Some (name ^ "_s"), mk_union_fields m fields), Ident name
  | _ ->
      mk_spec_and_declarator m name t

(* A variant dedicated to functions that avoids the conversion of function type
 * to pointer-to-function. *)
and mk_spec_and_declarator_f m cc name ret_t params =
  mk_spec_and_decl m name [] ret_t (fun d ->
    Function (cc, d, List.map (fun (n, t) -> mk_spec_and_declarator m n t) params))

(* Enforce the invariant that declarations are wrapped in compound statements
 * and cannot appear "alone". *)
and mk_compound_if (stmts: C.stmt list) (under_else: bool): C.stmt =
  match stmts with
  | [ Decl _ ] ->
      Compound stmts
  | [ If _ | IfElse _ as stmt ] when under_else ->
      (* Never wrap an if under else with braces, because it would defeat `else
        * if` on the same line. *)
      stmt
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
      Decl (qs, t, None, None, { maybe_unused = false }, [ Ident name, None, None ]);
      For (
        `Expr (Op2 (K.Assign, Name name, init)),
        test, incr, body)
    ]
  else
    For (
      `Decl (qs, t, None, None, { maybe_unused = false }, [ Ident name, None, Some (InitExpr init)]),
      test, incr, body)

(* Takes e_array of type (Buf t) *)
and mk_initializer t e_array e_size e_value: C.stmt =
  match e_size with
  | C.Constant (_, "1")
  | C.Cast (_, C.Constant (_, "1")) ->
      Expr (Op2 (K.Assign, Index (e_array, Constant (K.UInt32, "0")), e_value))

  | _ ->
      match e_value with
      | C.Constant (_, s)
      | C.Cast (_, C.Constant (_, s)) when int_of_string s = 0 ->
          mk_memset t e_array e_size (C.Constant (K.UInt8, "0"))

      | C.Name "Lib_IntVector_Intrinsics_vec128_zero"
      | C.Name "Lib_IntVector_Intrinsics_vec256_zero"
      | C.Name "Lib_IntVector_Intrinsics_vec512_zero" ->
          (* Same as above. This is important to avoid generating avx2 instructions when merely
             allocating simd state. Under the hood, the C memset will use suitable instructions to
             go fast. *)
          mk_memset t e_array e_size (C.Constant (K.UInt8, "0"))

      | C.Constant (K.UInt8, _)
      | C.Cast (_, C.Constant (K.UInt8, _)) ->
          mk_memset t e_array e_size e_value

      | _ ->
          mk_for_loop "_i" [] (Int K.UInt32) zero
            (Op2 (K.Lt, Name "_i", e_size))
            (Op1 (K.PreIncr, Name "_i"))
            (Expr (Op2 (K.Assign, Index (e_array, Name "_i"), e_value)))

and mk_memset t e_array e_size e_init =
  let e_size =
    (* Commenting out this optimization below, because:
     *   error: ‘memset’ used with length equal to number of elements without
     *   multiplication by element size [-Werror=memset-elt-size]
     * is it not known that sizeof uint8_t = 1 ? *)
    (* match e_init with
    | C.Constant (K.UInt8, _) ->
        e_size
    | _ -> *)
        Op2 (K.Mult, e_size, Sizeof (Type t))
  in
  Expr (Call (Name "memset", [ e_array; e_init; e_size]))

and mk_check_size m t n_elements: C.stmt list =
  (* [init] is the default value for the elements of the array, and [n_elements] is
   * hopefully a constant *)
  let default = [ C.Expr (C.Call (C.Name "KRML_CHECK_SIZE", [ mk_sizeof m t; n_elements ])) ] in
  match bytes_in t, n_elements with
  | _, C.Cast (_, C.Constant (_, "1"))
  | _, C.Constant (_, "1") ->
      (* C compilers also don't seem to let the user define a type that would be
         greater than size_t, so if the element size is 1, then we can get rid
         of the check as well. *)
      []
  | Some w, C.Cast (_, C.Constant (_, n_elements))
  | Some w, C.Constant (_, n_elements) ->
      (* Compute, if we can, the size statically *)
      let size_bytes = Z.(of_int w * of_string n_elements) in
      let ptr_size = Z.(one lsl 16) in
      (* The C data model guarantees 16 bits wide for size_t, at least. *)
      if Z.( lt size_bytes ptr_size )then
        []
      else
        default
  | _ ->
      (* Nothing much we can deduce statically, bail *)
      default

and mk_sizeof m t =
  C.Sizeof (C.Type (mk_type m t))

and mk_sizeof_mul m t s =
  match s with
    | C.Constant (_, "1")
    | C.Cast (_, C.Constant (_, "1")) ->
        mk_sizeof m t
    | _ ->
        C.Op2 (K.Mult, mk_sizeof m t, s)

and mk_alloc_cast m t e =
  if !Options.cast_allocations then
    C.Cast (mk_type m (Pointer t), e)
  else
    e

and mk_malloc m t s =
  match t with
  | Qualified lid when Helpers.is_aligned_type lid ->
      let sz = Option.must (mk_alignment m t) in
      mk_alloc_cast m t (C.Call (C.Name "KRML_ALIGNED_MALLOC", [ sz; mk_sizeof_mul m t s ]))
  | _ ->
      mk_alloc_cast m t (C.Call (C.Name "KRML_HOST_MALLOC", [ mk_sizeof_mul m t s ]))

and mk_calloc m t s =
  mk_alloc_cast m t (C.Call (C.Name "KRML_HOST_CALLOC", [ s; mk_sizeof m t ]))

and mk_free t e =
  match t with
  | Qualified lid when Helpers.is_aligned_type lid ->
      C.Call (C.Name "KRML_ALIGNED_FREE", [ e ])
  | _ ->
      C.Call (C.Name "KRML_HOST_FREE", [ e ])

and mk_ignore is_var e =
  if is_var then
    C.Call (C.Name "KRML_MAYBE_UNUSED_VAR", [ e ])
  else
    C.Call (C.Name "KRML_HOST_IGNORE", [ e ])

(* NOTE: this is only legal because we rule out the creation of zero-length
 * heap-allocated buffers; if we were to allow that, then this begs the question
 * of whether memset(malloc(0), 0, 0) is UB or not! The result of malloc(0) is
 * implementation-defined, not undefined behavior. *)
and mk_eternal_bufcreate m buf (t: CStar.typ) init size =
  let size = mk_expr m size in
  let e, extra_stmt = match init with
    | Constant (_, "0") ->
        (* NOTE: we MUST NOT catch vector types here because there is no aligned_calloc! *)
        mk_calloc m t size, []
    | Any | Cast (Any, _) ->
        mk_malloc m t size, []
    | _ ->
        mk_malloc m t size,
        [ mk_initializer (mk_type m t) (mk_expr m buf) size (mk_expr m init) ]
  in
  mk_check_size m t size, e, extra_stmt

and assert_pointer t =
  match t with
  | Array (t, _)
  | Pointer t ->
      t
  | _ ->
      Warn.fatal_error "let-bound bufcreate has type %s instead of Pointer" (show_typ t)

and ensure_array t size =
  match t with
  | Pointer t ->
      Array (t, size)
  | Array _ as t ->
      t
  | t ->
      Warn.fatal_error "impossible: %s" (show_typ t)

and decay_array t =
  match t with
  | Array (t, _) ->
      Pointer t
  | t ->
      Warn.fatal_error "impossible: %s" (show_typ t)

and assert_array t =
  match t with
  | Array (t, _) ->
      t
  | t ->
      Warn.fatal_error "impossible: not an array %s" (show_typ t)

and is_aligned_type = function
  | Qualified lid ->
      Helpers.is_aligned_type lid
  | _ ->
      false

and mk_alignment m t: C11.expr option =
  if is_aligned_type t then
    match t with
    | Qualified (["Lib"; "IntVector"; "Intrinsics"], "vec128") ->
        Some (Constant (CInt, "16"))
    | Qualified (["Lib"; "IntVector"; "Intrinsics"], "vec256") ->
        Some (Constant (CInt, "32"))
    | Qualified (["Lib"; "IntVector"; "Intrinsics"], "vec512") ->
        Some (Constant (CInt, "64"))
    | _ ->
        Some (Sizeof (Type (mk_type m t)))
  else
    None

and mk_stmt m (stmt: stmt): C.stmt list =
  match stmt with
  | Comment s ->
      [ Comment s ]

  | Return e ->
      let e = Option.map (fun e ->
        let e = mk_expr m e in
        if Options.debug "c-calls" then
          C.Call (Name "KRML_DEBUG_RETURN", [ e ])
        else
          e
      ) e in
      [ Return e ]

  | Block stmts ->
      [ Compound (mk_stmts m stmts) ]

  | Break ->
      [ Break ]

  | Continue ->
      [ Continue ]

  (* Ignore injects `expr`s into `stmt`s by ignoring their return value. No need
     to double-ignore, since C does it for us automatically, and C compilers
     treat this as 100% normal UNLESS the programmer uses extensions like
     `__attribute__((nodiscard))`. *)
  | Ignore (Call (Qualified ([ "LowStar"; "Ignore" ], "ignore"), [ arg; _ ])) when is_call arg ->
      [ Expr (mk_expr m arg) ]

  | Ignore e ->
      [ Expr (mk_expr m e) ]

  | Decl (binder, BufCreate ((Eternal | Heap), init, size)) ->
      let t = assert_pointer binder.typ in
      let stmt_check, expr_alloc, stmt_extra =
        mk_eternal_bufcreate m (Var binder.name) t init size
      in
      let qs, spec, decl = mk_spec_and_declarator m binder.name binder.typ in
      let decl: C.stmt list = [ Decl (qs, spec, None, None, { maybe_unused = false }, [ decl, None, Some (InitExpr expr_alloc)]) ] in
      stmt_check @ decl @ stmt_extra

  | Decl (binder, BufCreate (Stack, init, size)) ->
      (* In the case where this is a buffer creation in the C* meaning, then we
       * declare a fixed-length array; this is an "upcast" from pointer type to
       * array type, in the C sense. *)
      let t = ensure_array binder.typ size in
      let alignment = mk_alignment m (assert_array t) in
      let is_constant = match size with Constant _ -> true | _ -> false in
      let use_alloca = not is_constant && !Options.alloca_if_vla in
      let (maybe_init, needs_init): C.init option * _ = match init, size with
        | _, Constant (_, "0") (* zero-sized array... legal for malloc *)
        | Cast (Any, _), _
        | Any, _ ->
            (* No initial value needed in the declarator; no further
             * initialization needed either. *)
            None, false

        | (Constant (_, "0") |
          Qualified (["Lib"; "IntVector"; "Intrinsics"],
            ("vec128_zero" | "vec256_zero" | "vec512_zero"))),
          Constant _ when not use_alloca ->
            (* The only case the we can initialize statically is a known, static
             * size _and_ a zero initializer. If we're about to alloca, don't
             * use a zero-initializer. *)
            Some (Initializer [ InitExpr (C.Constant (K.UInt32, "0")) ]), false

        | _ ->
            None, true
      in
      let size = mk_expr m size in
      let t, maybe_init =
        (* If we're doing an alloca, override the initial value (it's now the
         * call to alloca) and decay the array to a pointer type. *)
        if use_alloca then
          if alignment <> None then
            Warn.fatal_error "In the following statement, the variable-length \
              array on the stack (VLA) must be aligned, but -falloca mandates the \
              use of alloca, which krml cannot yet align\n%s\n"
              (show_stmt stmt)
          else
            let bytes = mk_alloc_cast m (assert_pointer t) (C.Call (C.Name "alloca", [
              C.Op2 (K.Mult, size, C.Sizeof (C.Type (mk_type m (assert_pointer t)))) ])) in
            assert (maybe_init = None);
            decay_array t, Some (InitExpr bytes)
        else
          t, maybe_init
      in
      let init = mk_expr m init in
      let qs, spec, decl = mk_spec_and_declarator m binder.name t in
      let extra_stmt: C.stmt list =
        if needs_init then
          [ mk_initializer (mk_type m (assert_pointer t)) (Name binder.name) size init ]
        else
          []
      in
      let decl: C.stmt list = [ Decl (qs, spec, None, None, { maybe_unused = false }, [ decl, alignment, maybe_init ]) ] in
      mk_check_size m (assert_pointer binder.typ) size @
      decl @
      extra_stmt

  | Decl (_, BufCreateL ((Eternal | Heap), _)) as s ->
      failwith ("TODO: the array below is either in the eternal or heap region, \
        uses createL, but we don't have (yet) codegen for this:\n" ^
        CStar.show_stmt s)

  | Decl (binder, BufCreateL (Stack, inits)) ->
      (* Per the C standard, static initializers guarantee for missing fields
       * that they're initialized as if they had static storage duration, i.e.
       * with zero. *)
      let t = ensure_array binder.typ (Constant (K.uint32_of_int (List.length inits))) in
      let alignment = mk_alignment m (assert_array t) in
      let inits = trim_trailing_zeros inits in
      let qs, spec, decl = mk_spec_and_declarator m binder.name t in
      [ Decl (qs, spec, None, None, { maybe_unused = false }, [ decl, alignment, Some (Initializer (List.map (fun e ->
        InitExpr (mk_expr m e)
      ) inits))])]

  | Decl (binder, e) ->
      let qs, spec, decl = mk_spec_and_declarator m binder.name binder.typ in
      let init: init option = match e with Any -> None | _ -> Some (struct_as_initializer m e) in
      [ Decl (qs, spec, None, None, { maybe_unused = false }, [ decl, None, init ]) ]

  | IfThenElse (false, e, b1, b2) ->
      if List.length b2 > 0 then
        [ IfElse (mk_expr m e, mk_compound_if (mk_stmts m b1) false, mk_compound_if (mk_stmts m b2) true) ]
      else
        [ If (mk_expr m e, mk_compound_if (mk_stmts m b1) false) ]

  | IfThenElse (true, e, b1, b2) ->
      let rec find_elif acc = function
        | [ IfThenElse (true, e, b1, b2) ] ->
            let acc = (mk_expr m e, mk_stmts m b1) :: acc in
            find_elif acc b2
        | b ->
            List.rev acc, mk_stmts m b
      in
      let elif_blocks, else_block = find_elif [] b2 in
      [ IfDef (mk_expr m e, mk_stmts m b1, elif_blocks, else_block) ]

  | Assign (BufRead _, _, (Any | Cast (Any, _))) ->
      []

  | Assign (Var x, _, Call (Op K.Add, [ Var y; Constant (_, "1") ])) when x = y ->
      [ Expr (Op1 (PostIncr, Name x)) ]

  | Assign (Var x, _, Call (Op K.Sub, [ Var y; Constant (_, "1") ])) when x = y ->
      [ Expr (Op1 (PostDecr, Name x)) ]

  | Assign (e1, t, BufCreate (Eternal, init, size)) ->
      let v = assert_var m e1 in
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
      let vs = vars_of m init in
      if S.mem v vs then
        let t_elt = assert_pointer t in
        let name_init = "_init" ^ fresh () in
        let size = mk_expr m size in
        let stmt_init = mk_stmt m (Decl ({ name = name_init; typ = t_elt }, init)) in
        let stmt_assign = [ Expr (Assign (mk_expr m e1, mk_malloc m t_elt size)) ] in
        let stmt_fill = mk_initializer (mk_type m t_elt) (mk_expr m e1) size (mk_expr m (Var name_init)) in
        stmt_init @
        stmt_assign @
        [ stmt_fill ]
      else
        let stmt_check, expr_alloc, stmt_extra = mk_eternal_bufcreate m e1 (assert_pointer t) init size in
        stmt_check @
        [ Expr (Assign (mk_expr m e1, expr_alloc)) ] @
        stmt_extra

  | Assign (_, _, BufCreateL (Eternal, _)) ->
      failwith "TODO"

  | Assign (e1, _, e2) ->
      [ Expr (Assign (mk_expr m e1, mk_expr m e2)) ]

  | BufWrite (_, _, (Any | Cast (Any, _))) ->
      []

  | BufWrite (e1, e2, e3) ->
      [ Expr (Assign (mk_index m e1 e2, mk_expr m e3)) ]

  | BufBlit (t, e1, e2, e3, e4, e5) ->
      let dest = match e4 with
        | Constant (_, "0") -> mk_expr m e3
        | _ -> Op2 (K.Add, mk_expr m e3, mk_expr m e4)
      in
      let source = match e2 with
        | Constant (_, "0") -> mk_expr m e1
        | _ -> Op2 (K.Add, mk_expr m e1, mk_expr m e2)
      in
      [ Expr (Call (Name "memcpy", [
        dest;
        source;
        Op2 (K.Mult, mk_expr m e5, mk_sizeof m t)])) ]

  | BufFill (t, buf, v, size) ->
      (* Again, assuming that these are non-effectful. *)
      [ mk_initializer (mk_type m t) (mk_expr m buf) (mk_expr m size) (mk_expr m v) ]

  | BufFree (t, e) ->
      [ Expr (mk_free t (mk_expr m e)) ]

  | While (e1, e2) ->
      [ While (mk_expr m e1, mk_compound_if (mk_stmts m e2) false) ]

  | Switch (e, branches, default) ->
      [ Switch (
          mk_expr m e,
          List.map (fun (ident, block) ->
            (match ident with
            | `Ident ident -> Name (to_c_name m ident)
            | `Int k -> Constant k),
            let block = mk_stmts m block in
            if List.length block > 0 then
              match KList.last block with
              | Return _ -> Compound block
              | _ -> Compound (block @ [ Break ])
            else
              Compound [ Break ]
          ) branches,
          match default with
          | Some block ->
              Compound (mk_stmts m block)
          | _ ->
              let p = if !Options.c89_std then "KRML_HOST_PRINTF" else "KRML_HOST_EPRINTF" in
              Compound [
                Expr (Call (Name p, [
                  Literal "KaRaMeL incomplete match at %s:%d\\n"; Name "__FILE__"; Name "__LINE__"  ]));
                Expr (Call (Name "KRML_HOST_EXIT", [ Constant (K.UInt8, "253") ]))
              ]
      )]

  | Abort s ->
      let p = if !Options.c89_std then "KRML_HOST_PRINTF" else "KRML_HOST_EPRINTF" in
      [ Expr (Call (Name p, [
          Literal "KaRaMeL abort at %s:%d\\n%s\\n"; Name "__FILE__"; Name "__LINE__"; Literal (escape_string s) ]));
        Expr (Call (Name "KRML_HOST_EXIT", [ Constant (K.UInt8, "255") ])); ]

  | For (`Decl (binder, e1), e2, e3, b) ->
      let qs, spec, decl = mk_spec_and_declarator m binder.name binder.typ in
      let name = match decl with Ident name -> name | _ -> failwith "not an ident" in
      let init = match struct_as_initializer m e1 with InitExpr init -> init | _ -> failwith "not an initexpr" in
      let e2 = mk_expr m e2 in
      let e3 = match mk_stmt m e3 with [ Expr e3 ] -> e3 | _ -> assert false in
      let b = mk_compound_if (mk_stmts m b) false in
      [ mk_for_loop name qs spec init e2 e3 b ]

  | For (e1, e2, e3, b) ->
      let e1 = match e1 with
        | `Skip -> `Skip
        | `Stmt e1 -> `Expr (match mk_stmt m e1 with [ Expr e1 ] -> e1 | _ -> assert false)
        | _ -> assert false
      in
      let e2 = mk_expr m e2 in
      let e3 = match mk_stmt m e3 with [ Expr e3 ] -> e3 | _ -> assert false in
      let b = mk_compound_if (mk_stmts m b) false in
      [ For (e1, e2, e3, b) ]


and mk_stmts m stmts: C.stmt list =
  let stmts = KList.map_flatten (mk_stmt m) stmts in
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



and mk_index m (e1: expr) (e2: expr): C.expr =
  match e2 with
  | Qualified (["C"], "_zero_for_deref") ->
      mk_deref m e1
  | _ ->
    begin match mk_expr m e2 with
    | Cast (_, (Constant _ as c)) ->
        Index (mk_expr m e1, c)
    | e2' ->
        Index (mk_expr m e1, e2')
    end

and mk_deref m (e: expr) : C.expr =
  match mk_expr m e with
  | Address e' ->
      (* *&expr is equivalent to expr *)
      e'
  | e' ->
      Deref e'

(* Some functions get a special treatment and are pretty-printed in a specific
 * way at the very last minute. KaRaMeL is never supposed to generate unused
 * declarations, so these primitives must not be output in the resulting C
 * files. *)

and mk_expr m (e: expr): C.expr =
  match e with
  | InlineComment (s, e, s') ->
      InlineComment (s, mk_expr m e, s')

  | Call (Op o, [ e ]) ->
      Op1 (o, mk_expr m e)

  | Call (Op o, [ e1; e2 ]) ->
      Op2 (o, mk_expr m e1, mk_expr m e2)

  | Comma (e1, e2) ->
      Op2 (K.Comma, mk_expr m e1, mk_expr m e2)

  | Call (Qualified ([ "LowStar"; "Ignore" ], "ignore"), [ _ ]) ->
      (* Only one argument because of unit-to-void elimination -- should not happen. *)
      failwith "`ignore ()` should have been removed earlier on"

  | Call (Qualified ([ "LowStar"; "Ignore" ], "ignore"), [ arg; _ ]) ->
      mk_ignore (is_var arg) (mk_expr m arg)

  | Call (Qualified ([ "C"; "Nullity" ], s), [ e1 ]) when KString.starts_with s "op_Bang_Star__" ->
      mk_deref m e1

  | Call (Qualified ([ "LowStar"; "BufferOps" ], s), e1 :: _) when KString.starts_with s "op_Bang_Star__" ->
      mk_deref m e1

  | Call (Qualified ([ "LowStar"; "BufferOps" ], s), e1 :: e2 :: _ ) when KString.starts_with s "op_Star_Equals__" ->
      Op2 (K.Assign, mk_deref m e1, mk_expr m e2)

  | Call (Qualified ([ "C"; "String"], "of_literal"), [ StringLiteral _ as s ]) ->
      mk_expr m s

  | Call (Qualified ([ "C"; "Compat"; "String" ], "of_literal"), [ StringLiteral _ as s ]) ->
      mk_expr m s

  | Call (Qualified ([ "C"; "String" ], "get"), [ e1; e2 ])
  | Call (Qualified ([ "C"; "Compat"; "String" ], "get"), [ e1; e2 ])
  | BufRead (e1, e2) ->
      mk_index m e1 e2

  | BufNull ->
      Name "NULL"

  | Call (Qualified ( [ "Steel"; "ST"; "HigherArray" ], "intro_fits_u32"), _ ) ->
      Call (Name "static_assert", [Op2 (K.Lte, Name "UINT32_MAX", Name "SIZE_MAX")])
  | Call (Qualified ( [ "Steel"; "ST"; "HigherArray" ], "intro_fits_u64"), _ ) ->
      Call (Name "static_assert", [Op2 (K.Lte, Name "UINT64_MAX", Name "SIZE_MAX")])
  | Call (Qualified ( [ "Steel"; "ST"; "HigherArray" ], "intro_fits_ptrdiff32"), _ ) ->
      Call (Name "static_assert", [Op2 (K.Lte, Name "INT32_MAX", Name "PTRDIFF_MAX")])
  | Call (Qualified ( [ "Steel"; "ST"; "HigherArray" ], "intro_fits_ptrdiff64"), _ ) ->
      Call (Name "static_assert", [Op2 (K.Lte, Name "INT64_MAX", Name "PTRDIFF_MAX")])

  | Call (Qualified ( [ "FStar"; "UInt128" ], "add"), [ e1; e2 ]) when !Options.builtin_uint128 ->
      Op2 (K.Add, mk_expr m e1, mk_expr m e2)

  | Call (Qualified ( [ "FStar"; "UInt128" ], "mul"), [ e1; e2 ]) when !Options.builtin_uint128 ->
      Op2 (K.Mult, mk_expr m e1, mk_expr m e2)

  | Call (Qualified ( [ "FStar"; "UInt128" ], "add_mod"), [ e1; e2 ]) when !Options.builtin_uint128 ->
      Op2 (K.Add, mk_expr m e1, mk_expr m e2)

  | Call (Qualified ( [ "FStar"; "UInt128" ], "sub"), [ e1; e2 ]) when !Options.builtin_uint128 ->
      Op2 (K.Sub, mk_expr m e1, mk_expr m e2)

  | Call (Qualified ( [ "FStar"; "UInt128" ], "sub_mod"), [ e1; e2 ]) when !Options.builtin_uint128 ->
      Op2 (K.Sub, mk_expr m e1, mk_expr m e2)

  | Call (Qualified ( [ "FStar"; "UInt128" ], "logand"), [ e1; e2 ]) when !Options.builtin_uint128 ->
      Op2 (K.BAnd, mk_expr m e1, mk_expr m e2)

  | Call (Qualified ( [ "FStar"; "UInt128" ], "logor"), [ e1; e2 ]) when !Options.builtin_uint128 ->
      Op2 (K.BOr, mk_expr m e1, mk_expr m e2)

  | Call (Qualified ( [ "FStar"; "UInt128" ], "logxor"), [ e1; e2 ]) when !Options.builtin_uint128 ->
      Op2 (K.BXor, mk_expr m e1, mk_expr m e2)

  | Call (Qualified ( [ "FStar"; "UInt128" ], "lognot"), [ e1 ]) when !Options.builtin_uint128 ->
      Op1 (K.BNot, mk_expr m e1)

  | Call (Qualified ( [ "FStar"; "UInt128" ], "shift_left"), [ e1; e2 ]) when !Options.builtin_uint128 ->
      Op2 (K.BShiftL, mk_expr m e1, mk_expr m e2)

  | Call (Qualified ( [ "FStar"; "UInt128" ], "shift_right"), [ e1; e2 ]) when !Options.builtin_uint128 ->
      Op2 (K.BShiftR, mk_expr m e1, mk_expr m e2)

  | Call (Qualified ( [ "FStar"; "UInt128" ], "uint64_to_uint128"), [ e1 ]) when !Options.builtin_uint128 ->
      Cast (mk_type m (Qualified ([], "uint128_t")), mk_expr m e1)

  | Call (Qualified ( [ "FStar"; "UInt128" ], "uint128_to_uint64"), [ e1 ]) when !Options.builtin_uint128 ->
      Cast (mk_type m (Qualified ([], "uint64_t")), mk_expr m e1)

  | Call (Qualified ( [ "FStar"; "UInt128" ], "mul_wide"), [ e1; e2 ]) when !Options.builtin_uint128 ->
      Op2 (K.Mult, Cast (mk_type m (Qualified ([], "uint128_t")), mk_expr m e1), mk_expr m e2)

  | Call (e, es) ->
      Call (mk_expr m e, List.map (mk_expr m) es)

  | Var ident ->
      Name ident

  | Qualified ident
  | Macro ident ->
      Name (to_c_name m ident)

  | Constant (w, c) ->
      (* See discussion in AstToCStar.ml, around mk_arith. *)
      if K.is_unsigned w && w <> SizeT then
        Constant (w, c)
      else
        (* Not sure what to do with signed integer types. TBD. Mostly trying to
           avoid them being upcast into an unsigned type. *)
        Cast (([], Int w, Ident ""), Constant (w, c))

  | BufCreate _ | BufCreateL _ ->
      failwith "[mk_expr m]: Buffer.create and Buffer.createl may only appear as let ... = Buffer.create"

  | BufSub (e1, Constant (_, "0")) ->
      mk_expr m e1

  | BufSub (e1, e2) ->
      Op2 (K.Add, mk_expr m e1, mk_expr m e2)

  | Cast (e, t') ->
      (* JP: what is this? TODO review. *)
      begin match e with
      | Cast (_, t) as e when t = t' || t = Int Constant.UInt8 && t' = Pointer Void ->
          mk_expr m e
      | e ->
          Cast (mk_type m t', mk_expr m e)
      end

  | Any ->
      Cast (([], Void, Pointer ([], Ident "")), zero)

  | Op _ ->
      failwith "[mk_expr m]: op should've been caught"

  | Bool b ->
      Bool b

  | Struct (typ, fields) ->
      if typ = None then
        failwith ("Expected a type annotation for: \n" ^ show_expr e);
      let typ = Option.must typ in
      mk_compound_literal m typ fields

  | Field (BufRead (e, Constant (_, "0")), field) ->
      MemberAccessPointer (mk_expr m e, field)

  | Field (e, field) ->
      MemberAccess (mk_expr m e, field)

  | StringLiteral s ->
      Literal (escape_string s)

  | AddrOf e ->
      Address (mk_expr m e)

  | EAbort (t, s) ->
      Call (Name "KRML_EABORT", [ Type (mk_type m t); Literal (escape_string s) ])

  | Stmt s ->
      Stmt (KList.map_flatten (mk_stmt m) s)

  | Type t ->
      Type (mk_type m t)


and mk_compound_literal m name fields =
  let name = to_c_name m name in
  (* TODO really properly specify C's type_name! *)
  CompoundLiteral (([], Named name, Ident ""), fields_as_initializer_list m fields)

and struct_as_initializer m = function
  | Struct (_, fields) ->
      Initializer (fields_as_initializer_list m fields)
  | e ->
      InitExpr (mk_expr m e)

and fields_as_initializer_list m fields =
  List.map (function
    | Some field, e -> Designated (Dot field, struct_as_initializer m e)
    | None, e -> struct_as_initializer m e
  ) fields

and mk_type m t =
  (* hack alert *)
  mk_spec_and_declarator m "" t

let mk_comments =
  KList.filter_map (function
    | Comment c when c <> "" ->
        Some c
    | _ ->
        None
  )

let wrap_verbatim lid flags d =
  (if !Options.rst_snippets then
    [ Text (KPrint.bsprintf "/* SNIPPET_START: %s */" lid) ]
  else
    []) @
  KList.filter_map (function
    | Prologue s -> Some (Text s)
    | _ -> None
  ) flags @
  KList.filter_map (function
    | Deprecated s -> Some (Text (KPrint.bsprintf "KRML_DEPRECATED(\"%s\")" s))
    | _ -> None
  ) flags @
  [ d ] @ KList.filter_map (function
    | Epilogue s -> Some (Text s)
    | _ -> None
  ) flags @
  if !Options.rst_snippets then
    [ Text (KPrint.bsprintf "/* SNIPPET_END: %s */" lid) ]
  else
    [] @
  []

let enum_as_macros cases =
  let lines: string list = List.mapi (fun i c ->
    KPrint.bsprintf "#define %s %d" c i
  ) cases in
  String.concat "\n" lines

let strengthen_array t expr =
  match expr with
  | BufCreateL (_, es) ->
      ensure_array t (Constant (K.uint32_of_int (List.length es)))
  | BufCreate (_, _, size) ->
      ensure_array t size
  | _ ->
      t

(** Function definition or global definition. *)
let mk_function_or_global_body m (d: decl): C.declaration_or_function list =
  match d with
  | External _
  | TypeForward _
  | Type _ ->
      []

  | Function (cc, flags, return_type, name, parameters, body) ->
      if is_primitive name then
        []
      else
        let name = to_c_name m name in
        begin try
          let static = if List.exists ((=) Private) flags then Some Static else None in
          let inline =
            if List.mem NoInline flags then
              Some C11.NoInline
            else if List.mem Inline flags then
              Some C11.Inline
            else
              None
          in
          let parameters = List.map (fun { name; typ } -> name, typ) parameters in
          let qs, spec, decl = mk_spec_and_declarator_f m cc name return_type parameters in
          let body = ensure_compound (mk_debug name parameters @ mk_stmts m body) in
          let extra = { maybe_unused = List.mem MaybeUnused flags } in
          wrap_verbatim name flags (Function (mk_comments flags, (qs, spec, inline, static, extra, [ decl, None, None ]), body))
        with e ->
          beprintf "Fatal exception raised in %s\n" name;
          raise e
        end

  | Global (name, macro, flags, t, expr) ->
      if is_primitive name || macro then
        []
      else
        let name = to_c_name m name in
        let t = strengthen_array t expr in
        let alignment = if is_array t then mk_alignment m (assert_array t) else None in
        let qs, spec, decl = mk_spec_and_declarator m name t in
        let static = if List.exists ((=) Private) flags then Some Static else None in
        let extra = { maybe_unused = List.mem MaybeUnused flags } in
        match expr with
        | Any ->
            wrap_verbatim name flags (Decl (mk_comments flags, (qs, spec, None, static, extra, [ decl, alignment, None ])))
        | BufCreateL (_, es) ->
            let es = trim_trailing_zeros es in
            let es = List.map (struct_as_initializer m) es in
            wrap_verbatim name flags (Decl (mk_comments flags, (qs, spec, None, static, extra, [
              decl, alignment, Some (Initializer es) ])))
        (* Global static arrays of arithmetic type are initialized implicitly to 0 *)
        | BufCreate (_, Constant (_, "0"), _)
        | BufCreate (_, CStar.Bool false, _)
        | BufCreate (_, CStar.Any, _) ->
            wrap_verbatim name flags (Decl (mk_comments flags, (qs, spec, None, static, extra, [
              decl, alignment, None ])))
        | _ ->
            let expr = struct_as_initializer m expr in
            wrap_verbatim name flags (Decl (mk_comments flags, (qs, spec, None, static, extra, [ decl, alignment, Some expr ])))

(** Function prototype, or extern global declaration (no definition). *)
let mk_function_or_global_stub m (d: decl): C.declaration_or_function list =
  match d with
  | External _
  | TypeForward _
  | Type _ ->
      []

  | Function (cc, flags, return_type, name, parameters, _) ->
      if is_primitive name then
        []
      else
        let name = to_c_name m name in
        begin try
          let parameters = List.map (fun { name; typ } -> name, typ) parameters in
          let qs, spec, decl = mk_spec_and_declarator_f m cc name return_type parameters in
          (* JP: shouldn't we check for the presence of `inline` here? What does
           * the C standard say? inline on prototype and declaration? *)
          (* Regarding __attribute__((unused)), either one is enough. *)
          wrap_verbatim name flags (Decl (mk_comments flags, (qs, spec, None, None, { maybe_unused = false }, [ decl, None, None ])))
        with e ->
          beprintf "Fatal exception raised in %s\n" name;
          raise e
        end

  | Global (name, macro, flags, t, expr) ->
      if is_primitive name || macro then
        []
      else
        let name = to_c_name m name in
        let t = strengthen_array t expr in
        let qs, spec, decl = mk_spec_and_declarator m name t in
        wrap_verbatim name flags (Decl (mk_comments flags, (qs, spec, None, Some Extern, { maybe_unused = false }, [ decl, None, None ])))

type where = H | C

let declared_in_library lid =
  List.exists (fun b -> Bundle.pattern_matches b (String.concat "_" (fst lid))) !Options.library

let hand_written lid =
  List.exists (fun b -> Bundle.pattern_matches b (String.concat "_" (fst lid))) !Options.hand_written

(* Type declarations, external function declarations. These are the things that
 * are either declared in the header (public), or in the c file (private), but
 * not twice. *)
let mk_type_or_external m (w: where) ?(is_inline_static=false) (d: decl): C.declaration_or_function list =
  let mk_forward_decl name flags k =
    let d = match k with
      | FStruct -> C.Struct (Some (name ^ "_s"), None)
      | FUnion -> C.Union (Some (name ^ "_s"), None)
    in
    wrap_verbatim name flags (Decl ([], ([], d, None, Some Typedef, { maybe_unused = false }, [ Ident name, None, None ])))
  in
  match d with
  | TypeForward (name, flags, k) ->
      let name = to_c_name m name in
      mk_forward_decl name flags k
  | Type (name, Struct _, flags) when w = H && List.mem AbstractStruct flags ->
      let name = to_c_name m name in
      mk_forward_decl name flags FStruct
  | Type (name, t, flags) ->
      if is_primitive name || (is_inline_static && declared_in_library name) then
        []
      else begin
        let name = to_c_name m name in
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
            let cases = List.map (to_c_name m) cases in
            wrap_verbatim name flags (Text (enum_as_macros cases)) @
            let qs, spec, decl = mk_spec_and_declarator_t m name (Int t) in
            [ Decl ([], (qs, spec, None, Some Typedef, { maybe_unused = false }, [ decl, None, None ]))]
        | _ ->
            let qs, spec, decl = mk_spec_and_declarator_t m name t in
            wrap_verbatim name flags (Decl (mk_comments flags, (qs, spec, None, Some Typedef, { maybe_unused = false }, [ decl, None, None ])))
      end

  | External (name, Function (cc, t, ts), flags, pp) ->
      if is_primitive name ||
        (is_inline_static && declared_in_library name && not (hand_written name))
      then
        []
      else
        let name = to_c_name m name in
        let missing_names = List.length ts - List.length pp in
        let arg_names =
          if missing_names >= 0 then
            pp @ KList.make missing_names (fun i -> KPrint.bsprintf "x%d" i)
          else
            (* For functions that take a single unit argument, the name of the
             * unit is gone. *)
            fst (KList.split (List.length ts) pp)
        in
        let qs, spec, decl = mk_spec_and_declarator_f m cc name t (List.combine arg_names ts) in
        let inline =
          if List.mem NoInline flags then
            Some C11.NoInline
          else
            None
        in
        wrap_verbatim name flags (Decl (mk_comments flags, (qs, spec, inline, Some Extern, { maybe_unused = false }, [ decl, None, None ])))

  | External (name, t, flags, _) ->
      if is_primitive name ||
        (is_inline_static && declared_in_library name && not (hand_written name))
      then
        []
      else
        let name = to_c_name m name in
        let qs, spec, decl = mk_spec_and_declarator m name t in
        wrap_verbatim name flags (Decl (mk_comments flags, (qs, spec, None, Some Extern, { maybe_unused = false }, [ decl, None, None ])))

  | Global (name, macro, flags, _, body) when macro && not (is_inline_static && declared_in_library name) ->
      (* Macros behave like types, they ought to be declared once. *)
      let name = to_c_name m name in
      wrap_verbatim name flags (Macro (mk_comments flags, name, mk_expr m body))

  | Function _ | Global _ ->
      []


let flags_of_decl (d: CStar.decl) =
  match d with
  | Global (_, _, flags, _, _)
  | Function (_, flags, _, _, _, _)
  | Type (_, _, flags)
  | TypeForward (_, flags, _)
  | External (_, _, flags, _) ->
      flags

(* A mini-DSL to expression control-flow for generation of C declarations in the
 * presence of visibility, C abstract structs, and potentially static headers.
 * *)
let either f1 f2 x =
  match f1 x with
  | [] -> f2 x
  | l -> l

let if_private_or_abstract_struct f d =
  let flags = flags_of_decl d in
  if List.mem Private flags || List.mem AbstractStruct flags then
    f d
  else
    []

let if_public f d =
  if not (List.mem Private (flags_of_decl d)) && not (List.mem Internal (flags_of_decl d)) then
    f d
  else
    []

let if_internal f d =
  if List.mem Internal (flags_of_decl d) then
    f d
  else
    []

let none _ = []

let if_header_inline_static m f1 f2 d =
  let lid = lid_of_decl d in
  let is_inline_static =
    List.exists (fun p ->
      (* Only things that end up in headers are in the reverse-map. *)
      Hashtbl.mem m lid &&
      Bundle.pattern_matches p (String.concat "_" (fst lid)))
    !Options.static_header ||
    List.mem lid [
      [ "FStar"; "UInt8" ], "eq_mask";
      [ "FStar"; "UInt8" ], "gte_mask";
      [ "FStar"; "UInt16" ], "eq_mask";
      [ "FStar"; "UInt16" ], "gte_mask";
      [ "FStar"; "UInt32" ], "eq_mask";
      [ "FStar"; "UInt32" ], "gte_mask";
      [ "FStar"; "UInt64" ], "eq_mask";
      [ "FStar"; "UInt64" ], "gte_mask";
    ]
  in
  if is_inline_static then
    f1 d
  else
    f2 d

(* Building a .c file *)
let mk_file m decls =
  (* In the C file, we put function bodies, global bodies, and type
   * definitions and external definitions that were private to the file only.
   * *)
  KList.map_flatten
    (if_header_inline_static m
      none
      (either
        (mk_function_or_global_body m)
        (if_private_or_abstract_struct (mk_type_or_external m C))))
    decls

let mk_files (map: GlobalNames.mapping) files =
  List.map (fun (name, program) -> name, mk_file map program) files

(* Building three flavors of headers. *)

let mk_static f d =
  let promote_inline inline =
    match inline with
    | None | Some C11.Inline -> Some C11.Inline
    | Some NoInline -> Some NoInline
  in

  KList.map_flatten (function
    | C.Decl (comments, (qs, ts, inline, (None | Some (Static | Extern)), extra, decl_inits)) ->
        let is_func = match decl_inits with
          | [ Function _, _, _ ] -> promote_inline inline
          | [ _ ] -> inline
          | _ -> assert false
        in
        [ C.Decl (comments, (qs, ts, is_func, Some Static, extra, decl_inits)) ]
    | C.Function (comments, (qs, ts, inline, (None | Some (Static | Extern)), extra, decl_inits), body) ->
        (* We make the function static *and* inline UNLESS the user requested
           NoInline *)
        [ C.Function (comments, (qs, ts, promote_inline inline, Some Static, extra, decl_inits), body) ]
    | d ->
        [ d ]
  ) (f d)

(* Generates either a static header (the union of public + internal), OR just
   the public part. *)
let mk_public_header (m: GlobalNames.mapping) decls =
  (* In the header file, we put functions and global stubs, along with type
   * definitions that are visible from the outside. *)
  (* What should be the behavior for a type declaration marked as CAbstract but
   * whose module has -static-header? This ignores CAbstract. *)
  (* Note that static_header + library means that corresponding declarations are
   * effectively dropped on the basis that the user is doing separate extraction
   * & compilation + providing the required header. *)
  KList.map_flatten
    (if_public (
      (if_header_inline_static m
        (mk_static (either (mk_function_or_global_body m) (mk_type_or_external m ~is_inline_static:true C)))
        (either (mk_function_or_global_stub m) (mk_type_or_external m H)))))
    decls

(* Private part if not already a static header, empty otherwise. *)
let mk_internal_header (m: GlobalNames.mapping) decls =
  KList.map_flatten
    (if_internal (
      (if_header_inline_static m
        (mk_static (either (mk_function_or_global_body m) (mk_type_or_external m ~is_inline_static:true C)))
        (either (mk_function_or_global_stub m) (mk_type_or_external m H)))))
    decls

let mk_headers (map: GlobalNames.mapping)
  (files: (string * CStar.decl list) list)
=
  (* Generate headers with a sensible order for the message "WRITING H FILES: ...". *)
  let headers = List.fold_left (fun acc (name, program) ->
    let h = mk_public_header map program in
    let acc = if List.length h > 0 then (name, Public h) :: acc else acc in
    let h = mk_internal_header map program in
    let acc = if List.length h > 0 then (name, C.Internal h) :: acc else acc in
    acc
  ) [] files in
  List.rev headers

let drop_empty_headers deps headers: Bundles.deps Bundles.StringMap.t =
  let open Bundles in
  (* Refine dependencies to ignore now-gone empty headers. *)
  let not_dropped_internal f = List.exists (function
    | (name, C.Internal _) when f = name -> true
    | _ -> false
  ) headers in
  let not_dropped_public f = List.exists (function
    | (name, Public _) when f = name -> true
    | _ -> false
  ) headers in
  StringMap.map (fun { internal; public } -> {
    internal = StringSet.filter not_dropped_internal internal;
    public = StringSet.filter not_dropped_public public
  }) deps


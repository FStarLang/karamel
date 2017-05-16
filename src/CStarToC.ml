(** Converting from C* to C abstract syntax. *)

open C
open CStar
open KPrint
open Common

let zero = C.Constant (K.UInt8, "0")

let is_array = function Array _ -> true | _ -> false

let escape_string s =
  (* TODO: dive into the C lexical conventions + fix the F\* lexer *)
  String.escaped s

type rec_name = {
  lid: CStar.ident;
  typ: C.type_spec;
  used: bool ref;
}

(* Turns the ML declaration inside-out to match the C reading of a type.
 * See en.cppreference.com/w/c/language/declarations *)
let rec mk_spec_and_decl name rec_name (t: typ) (k: C.declarator -> C.declarator): C.type_spec * C.declarator =
  match t with
  | Pointer t ->
      mk_spec_and_decl name rec_name t (fun d -> Pointer (k d))
  | Array (t, size) ->
      (* F* guarantees that the initial size of arrays is always something
       * reasonable (i.e. <4GB). *)
      let size = match size with
        | Constant k -> C.Constant k
        | _ -> mk_expr size
      in
      mk_spec_and_decl name rec_name t (fun d -> Array (k d, size))
  | Function (cc, t, ts) ->
      (* Function types are pointers to function types, except in the top-level
       * declarator for a function, which gets special treatment via
       * mk_spec_and_declarator_f. *)
      mk_spec_and_decl name rec_name t (fun d ->
        Pointer (Function (cc, k d, List.mapi (fun i t ->
          mk_spec_and_decl (KPrint.bsprintf "x%d" i) rec_name t (fun d -> d)) ts)))
  | Int w ->
      Int w, k (Ident name)
  | Void ->
      Void, k (Ident name)
  | Qualified l ->
      begin match rec_name with
      | Some { lid; typ; used } when lid = l ->
          used := true;
          typ, k (Ident name)
      | _ ->
          Named l, k (Ident name)
      end
  | Enum tags ->
      Enum (None, tags), k (Ident name)
  | Z ->
      Named "mpz_t", k (Ident name)
  | Bool ->
      Named "bool", k (Ident name)
  | Struct fields ->
      Struct (None, mk_fields rec_name fields), k (Ident name)
  | Union fields ->
      Union (None, List.map (fun (name, typ) ->
        let spec, decl = mk_spec_and_decl name rec_name typ (fun d -> d) in
        spec, None, [ decl, None ]
      ) fields), k (Ident name)

and mk_fields rec_name fields =
  Some (List.map (fun (name, typ) ->
    let name = match name with Some name -> name | None -> "" in
    let spec, decl = mk_spec_and_decl name rec_name typ (fun d -> d) in
    spec, None, [ decl, None ]
  ) fields)

(* Standard spec/declarator pair (e.g. int x). *)
and mk_spec_and_declarator name t =
  mk_spec_and_decl name None t (fun d -> d)

(* A variant dedicated to typedef's, where the name really represents the type
 * itself. Such definitions may contain recursive occurrences of the type
 * itself; one can compile such a type definition to C when the type is a
 * struct, by naming it. *)
and mk_spec_and_declarator_t name t =
  match t with
  | Struct fields ->
      let name_s = name ^ "_s" in
      let used = ref false in
      let rec_name = Some { lid = name; typ = C.Struct (Some name_s, None); used } in
      (* Fills in [used]. *)
      let fields = mk_fields rec_name fields in
      if !used then
        C.Struct (Some name_s, fields), Ident name
      else
        C.Struct (None, fields), Ident name
  | _ ->
      mk_spec_and_declarator name t

(* A variant dedicated to functions that avoids the conversion of function type
 * to pointer-to-function. *)
and mk_spec_and_declarator_f cc name ret_t params =
  mk_spec_and_decl name None ret_t (fun d ->
    Function (cc, d, List.map (fun (n, t) -> mk_spec_and_decl n None t (fun d -> d)) params))

(* Enforce the invariant that declarations are wrapped in compound statements
 * and cannot appear "alone". *)
and mk_compound_if (stmts: C.stmt list): C.stmt =
  match stmts with
  | [ Decl _ ] ->
      Compound stmts
  | [ stmt ] ->
      stmt
  | _ ->
      Compound stmts

and ensure_compound (stmts: C.stmt list): C.stmt =
  match stmts with
  | [ Compound _ as stmt ] ->
      stmt
  | _ ->
      Compound stmts

and mk_for_loop_initializer e_array e_size e_value: C.stmt =
  For (
    (Int K.UInt, None, [ Ident "_i", Some (InitExpr zero)]),
    Op2 (K.Lt, Name "_i", e_size),
    Op1 (K.PreIncr, Name "_i"),
    Expr (Op2 (K.Assign, Index (e_array, Name "_i"), e_value)))

and mk_memset_zero_initializer e_array e_size =
  Expr (Call (Name "memset", [
    e_array;
    Constant (K.UInt8, "0");
    Op2 (K.Mult,
      e_size,
      Sizeof (Index (e_array, zero)))]))

and mk_check_size init n_elements: C.stmt list =
  (* [init] is the default value for the elements of the array, and [n_elements] is
   * hopefully a constant *)
  let default = [ C.Expr (C.Call (C.Name "KRML_CHECK_SIZE", [ init; n_elements ])) ] in
  match init, n_elements with
  | C.Cast (_, C.Constant (w, _)), C.Cast (_, C.Constant (_, n_elements)) ->
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
  C.Call (C.Name "sizeof", [ C.Type t ])

and mk_stmt (stmt: stmt): C.stmt list =
  match stmt with
  | Comment s ->
      [ Comment s ]

  | Return e ->
      [ Return (Option.map mk_expr e) ]

  | Block stmts ->
      [ Compound (mk_stmts stmts) ]

  | Ignore e ->
      [ Expr (mk_expr e) ]

  | Decl (binder, BufCreate (Eternal, init, size)) ->
      let spec, decl = mk_spec_and_declarator binder.name binder.typ in
      let type_name =
        match binder.typ with
        | Array (t, _)
        | Pointer t -> mk_spec_and_declarator "" t
        | _ -> Warnings.fatal_error "let-bound bufcreate has type %s instead of Pointer" (show_typ binder.typ)
      in
      let size = mk_expr size in
      let e, extra_stmt = match init with
        | Constant (_, "0") ->
            C.Call (C.Name "calloc", [ size; mk_sizeof type_name ]), []
        | _ ->
            C.Call (C.Name "malloc", [
              C.Op2 (K.Mult, mk_sizeof type_name, size)
            ]), [ mk_for_loop_initializer (Name binder.name) size (mk_expr init) ]
      in
      let decl: C.stmt list = [ Decl (spec, None, [ decl, Some (InitExpr e)]) ] in
      mk_check_size (mk_expr init) size @
      decl @
      extra_stmt

  | Decl (binder, BufCreate (Stack, init, size)) ->
      (* In the case where this is a buffer creation in the C* meaning, then we
       * declare a fixed-length array; this is an "upcast" from pointer type to
       * array type, in the C sense. *)
      let t = match binder.typ with
        | Pointer t -> Array (t, size)
        | Array _ as t -> t
        | t -> Warnings.fatal_error "impossible: %s" (show_typ t)
      in
      let module T = struct type init = Nope | Memset | Forloop end in
      let (maybe_init, init_type): C.init option * T.init = match init, size with
        | _, Constant (_, "0") ->
            (* zero-sized array *)
            None, T.Nope
        | Constant ((_, "0") as k), Constant _ ->
            (* The only case the we can initialize statically is a known, static
             * size _and_ a zero initializer. *)
            Some (Initializer [ InitExpr (C.Constant k) ]), T.Nope
        | Constant (_, "0"), _ ->
            None, T.Memset
        | _ ->
            None, T.Forloop
      in
      let size = mk_expr size in
      let init = mk_expr init in
      let spec, decl = mk_spec_and_declarator binder.name t in
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
      let decl: C.stmt list = [ Decl (spec, None, [ decl, maybe_init ]) ] in
      mk_check_size init size @
      decl @
      extra_stmt

  | Decl (binder, BufCreateL (l, inits)) ->
      if l <> Stack then
        failwith "TODO: createL / eternal";
      let t = match binder.typ with
        | Pointer t -> Array (t, Constant (K.uint32_of_int (List.length inits)))
        | Array _ as t -> t
        | t -> Warnings.fatal_error "impossible: %s" (show_typ t)
      in
      let spec, decl = mk_spec_and_declarator binder.name t in
      [ Decl (spec, None, [ decl, Some (Initializer (List.map (fun e ->
        InitExpr (mk_expr e)
      ) inits))])]

  | Decl (binder, e) ->
      let spec, decl = mk_spec_and_declarator binder.name binder.typ in
      let init: init option = match e with Any -> None | _ -> Some (struct_as_initializer e) in
      [ Decl (spec, None, [ decl, init ]) ]

  | IfThenElse (e, b1, b2) ->
      if List.length b2 > 0 then
        [ IfElse (mk_expr e, mk_compound_if (mk_stmts b1), mk_compound_if (mk_stmts b2)) ]
      else
        [ If (mk_expr e, mk_compound_if (mk_stmts b1)) ]

  | Copy (e1, _, BufCreate (Stack, init, size)) ->
      begin match e1 with
      | Var _ -> ()
      | _ -> failwith "TODO: for (int i = 0, t tmp = e1; i < ...; ++i) tmp[i] = "
      end;
      begin match init with
      | Constant (_, "0") ->
          mk_check_size (mk_expr init) (mk_expr size) @
          [ mk_memset_zero_initializer (mk_expr e1) (mk_expr size) ]
      | _ ->
          (* JP: why is this not a call to memcpy? *)
          mk_check_size (mk_expr init) (mk_expr size) @
          [ mk_for_loop_initializer (mk_expr e1) (mk_expr size) (mk_expr init) ]
      end

  | Copy (e1, typ, BufCreateL (Stack, elts)) ->
      (* int x[5]; *)
      (* memcpy(x, &((int[5]){ 1, 2, 3, 4, 5 }), sizeof x); *)
      [ Expr (Call (Name "memcpy", [
          mk_expr e1;
          CompoundLiteral (
            mk_type typ,
            List.map (fun e -> InitExpr (mk_expr e)) elts);
          Sizeof (mk_expr e1)]))]

  | Copy _ ->
      failwith "impossible"

  | Assign (e1, e2) ->
      [ Expr (Assign (mk_expr e1, mk_expr e2)) ]

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
      [ For (
          (Int K.UInt, None, [ Ident "_i", Some (InitExpr zero)]),
          Op2 (K.Lt, Name "_i", size),
          Op1 (K.PreIncr, Name "_i"),
          Expr (Op2 (K.Assign, Index (buf, Name "_i"), v)))]


  | While (e1, e2) ->
      [ While (mk_expr e1, mk_compound_if (mk_stmts e2)) ]

  | PushFrame | PopFrame ->
      failwith "[mk_stmt]: nested frames to be handled by [mk_stmts]"

  | Switch (e, branches) ->
      [ Switch (
          mk_expr e,
          List.map (fun (ident, block) ->
            Name ident, Compound (mk_stmts block @ [ Break ])
          ) branches,
          Compound [
            Expr (Call (Name "printf", [
              Literal "KreMLin incomplete match at %s:%d\\n"; Name "__FILE__"; Name "__LINE__"  ]));
            Expr (Call (Name "exit", [ Constant (K.UInt8, "253") ]))
          ]
      )]

  | Abort ->
      [ Expr (Call (Name "printf", [
          Literal "KreMLin abort at %s:%d\\n"; Name "__FILE__"; Name "__LINE__" ]));
        Expr (Call (Name "exit", [ Constant (K.UInt8, "255") ])); ]

  | For (binder, e1, e2, e3, b) ->
      let spec, decl = mk_spec_and_declarator binder.name binder.typ in
      let init = struct_as_initializer e1 in
      let e2 = mk_expr e2 in
      let e3 = match mk_stmt e3 with [ Expr e3 ] -> e3 | _ -> assert false in
      let b = mk_compound_if (mk_stmts b) in
      [ For ((spec, None, [ decl, Some init ]), e2, e3, b)]


and mk_stmts stmts: C.stmt list =
  match stmts with
  | PushFrame :: stmts ->
      let frame, remaining = mk_stmts' [] stmts in
      (* Not doing [Compound frame :: mk_stmts remaining] because of scoping
       * issues. *)
      frame @ mk_stmts remaining
  | stmt :: stmts ->
      mk_stmt stmt @ mk_stmts stmts
  | [] ->
      []

(** Consume the list of statements until the next pop frame, and return the
 * translated statements within the frame, along with the remaining statements
 * after the frame. *)
and mk_stmts' acc stmts: C.stmt list * stmt list =
  match stmts with
  | PushFrame :: stmts ->
      let frame, remaining = mk_stmts' [] stmts in
      (* Same comment as above (scoping issue). *)
      mk_stmts' (frame :: acc) remaining
  | PopFrame :: stmts ->
      List.flatten (List.rev acc), stmts
  | stmt :: stmts ->
      mk_stmts' (mk_stmt stmt :: acc) stmts
  | [] ->
      failwith "[mk_stmts']: unmatched push_frame"


and mk_index (e1: expr) (e2: expr): C.expr =
  match mk_expr e2 with
  | Cast (_, (Constant _ as c)) ->
      Index (mk_expr e1, c)
  | _ ->
      Index (mk_expr e1, mk_expr e2)


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

  | Call (e, es) ->
      Call (mk_expr e, List.map mk_expr es)

  | Var ident ->
      Name ident

  | Qualified ident ->
      Name ident

  | Constant (w, c) ->
      Cast ((Int w, Ident ""), Constant (w, c))

  | BufCreate _ | BufCreateL _ ->
      failwith "[mk_expr]: Buffer.create; Buffer.createl may only appear as let ... = Buffer.create"

  | BufRead (e1, e2) ->
      mk_index e1 e2

  | BufSub (e1, Constant (_, "0")) ->
      mk_expr e1

  | BufSub (e1, e2) ->
      Op2 (K.Add, mk_expr e1, mk_expr e2)

  | Cast (e, t') ->
      begin match e with
      | Cast (_, t) as e when t = t' || t = Int Constant.UInt8 && t' = Pointer Void ->
          mk_expr e
      | e ->
          Cast (mk_type t', mk_expr e)
      end

  | Any ->
      Cast ((Void, Pointer (Ident "")), zero)

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

  | EAbort t ->
      Call (Name "KRML_EABORT", [ Type (mk_type t) ])


and mk_compound_literal name fields =
  (* TODO really properly specify C's type_name! *)
  CompoundLiteral ((Named name, Ident ""), fields_as_initializer_list fields)

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

(** .c files include their own header *)
let mk_decl_or_function (d: decl): C.declaration_or_function option =
  match d with
  | External _
  | Type _ ->
      None

  | Function (cc, flags, return_type, name, parameters, body) ->
      begin try
        let static = if List.exists ((=) Private) flags then Some Static else None in
        let inline = List.exists ((=) CInline) flags in
        let parameters = List.map (fun { name; typ } -> name, typ) parameters in
        let spec, decl = mk_spec_and_declarator_f cc name return_type parameters in
        let body = ensure_compound (mk_stmts body) in
        Some (Function (inline, (spec, static, [ decl, None ]), body))
      with e ->
        beprintf "Fatal exception raised in %s\n" name;
        raise e
      end

  | Global (name, flags, t, expr) ->
      let t = match t with Function _ -> Pointer t | _ -> t in
      let spec, decl = mk_spec_and_declarator name t in
      let static = if List.exists ((=) Private) flags then Some Static else None in
      match expr with
      | Any ->
          Some (Decl (spec, static, [ decl, None ]))
      | _ ->
          let expr = mk_expr expr in
          Some (Decl (spec, static, [ decl, Some (InitExpr expr) ]))


let mk_program decls =
  KList.filter_map mk_decl_or_function decls

let mk_files files =
  List.map (fun (name, program) -> name, mk_program program) files


let mk_stub_or_function (d: decl): C.declaration_or_function option =
  match d with
  | Type (name, t) ->
      let spec, decl = mk_spec_and_declarator_t name t in
      Some (Decl (spec, Some Typedef, [ decl, None ]))

  | Function (cc, flags, return_type, name, parameters, _) ->
      if List.exists ((=) Private) flags then
        None
      else
        begin try
          let parameters = List.map (fun { name; typ } -> name, typ) parameters in
          let spec, decl = mk_spec_and_declarator_f cc name return_type parameters in
          Some (Decl (spec, None, [ decl, None ]))
        with e ->
          beprintf "Fatal exception raised in %s\n" name;
          raise e
        end

  | External (name, Function (cc, t, ts)) ->
      let spec, decl = mk_spec_and_declarator_f cc name t (List.mapi (fun i t ->
        KPrint.bsprintf "x%d" i, t
      ) ts) in
      Some (Decl (spec, Some Extern, [ decl, None ]))

  | External (name, t) ->
      let spec, decl = mk_spec_and_declarator name t in
      Some (Decl (spec, Some Extern, [ decl, None ]))

  | Global (name, flags, t, _) ->
      if List.exists ((=) Private) flags then
        None
      else
        let t = match t with Function _ -> Pointer t | _ -> t in
        let spec, decl = mk_spec_and_declarator name t in
        Some (Decl (spec, Some Extern, [ decl, None ]))


let mk_header decls =
  KList.filter_map mk_stub_or_function decls

let mk_headers files =
  List.map (fun (name, program) -> name, mk_header program) files

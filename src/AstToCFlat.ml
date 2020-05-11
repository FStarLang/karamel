(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 License. *)

(** Going from CStar to CFlat *)

module CF = CFlat
module K = Constant
module LidMap = Idents.LidMap
module StringMap = Map.Make(String)

open CFlat.Sizes
open Ast
open PrintAst.Ops


(** Environments.
 *
 * Variable declarations are visited in infix order; this order is used for
 * numbering the corresponding Cflat local declarations. Wasm will later on take
 * care of register allocation. *)
type env = {
  binders: int list;
  enums: int LidMap.t;
    (** Enumeration constants are assigned a distinct integer. *)
  layouts: layout LidMap.t;
    (** Pre-computed layouts for struct and enum types. Enums can be written
     * atomically, but structs cannot. *)
  globals: string LidMap.t;
    (** There are two kinds of global declarations.
     * - Arrays have `buf t` type in Low*; they are referred to exclusively by
     *   their lid; they are compiled to strings in the data segment; their
     *   definition becomes a Global in WASM and references to them just read
     *   the Global.
     * - Values have non-array types (e.g. a value struct type, integer). When
     *   referred to by their lid, there is a value read.
     *   - For atomic values (e.g. integers), this is trivially compilable as a
     *     Global slot in WASM that is initialized to a constant then read at
     *     reference-time.
     *   - For struct values, we lay them out according to the KreMLin layout in
     *     a string. Because of the struct-by-address transformation, these will
     *     only be referred to via the AddressOf operator, meaning that any
     *     &Foo_bar should resolve to the address of the global in the data
     *     segment.
     *     So, for these structs, we lay them out in a string when we hit their
     *     definition, and remember this string in `globals`. Then, any
     *     occurrence of &Foo_bar is replaced in this module with a
     *     StringLiteral. The strings are shared in memory at compile-time, and
     *     hashconsing in CFlatToWasm guarantees that they are shared in the
     *     resulting code, too. *)
  names: (lident, ident) Hashtbl.t;
}

and layout =
  | LEnum
  | LFlat of flat_layout
  | LBuiltin of size * array_size

and flat_layout = {
  size: int;
    (** In bytes *)
  fields: (string * offset) list;
    (** Any struct must be laid out on a word boundary (64-bit). Then, fields
     * can be always accessed using the most efficient offset computation. *)
}

and offset = int
  (** In byte *)

let empty names = {
  binders = [];
  enums = LidMap.empty;
  layouts = LidMap.empty;
  globals = LidMap.empty;
  names
}

(** Layouts and sizes. *)

let builtin_layouts = [
  ([ "C"; "String" ], "t"), I32, A32;
  ([ "C"; "String" ], "t_"), I32, A32;
  ([ "C"; "Compat"; "String" ], "t"), I32, A32;
  ([ "C"; "Compat"; "String" ], "t_"), I32, A32;
  ([ "Prims" ], "string"), I32, A32;
  ([ "Prims" ], "int"), I32, A32; (* should remove *)
  ([ "C" ], "clock_t"), I32, A32;
  ([ "C" ], "exit_code"), I32, A32;
]


(** The size of a type that fits in one WASM value. *)
let size_of (env: env) (t: typ): size =
  match t with
  | TInt w ->
      size_of_width w
  | TArray _ | TBuf _ ->
      I32
  | TBool | TUnit ->
      I32
  | TAnonymous (Enum _) ->
      I32
  | TQualified lid ->
      begin match LidMap.find lid env.layouts with
      | exception Not_found ->
          failwith (KPrint.bsprintf "size_of: %a not found" plid lid)
      | LEnum -> I32
      | LBuiltin (s, _) -> s
      | LFlat _ ->
          failwith (KPrint.bsprintf "size_of: this case should've been eliminated: %a" ptyp t)
      end
  | _ ->
      failwith (KPrint.bsprintf "size_of: this case should've been eliminated: %a" ptyp t)

(* The size of a type that fits in one WASM array cell. See [byte_size] for the
 * general version. *)
let array_size_of (env: env) (t: typ): array_size =
  match t with
  | TInt w ->
      array_size_of_width w
  | TArray _ | TBuf _ ->
      A32
  | TBool | TUnit ->
      A8
  | TAnonymous (Enum _) ->
      A32
  | TQualified lid ->
      begin match LidMap.find lid env.layouts with
      | exception Not_found ->
          failwith (KPrint.bsprintf "size_of: %a not found" plid lid)
      | LEnum -> A32
      | LBuiltin (_, s) -> s
      | LFlat _ ->
          failwith (KPrint.bsprintf "array_size_of: this case should've been eliminated: %a" ptyp t)
      end
  | _ ->
      failwith (KPrint.bsprintf "array_size_of: this case should've been eliminated: %a" ptyp t)

(* The alignment takes an array size, an our invariant is that integers are
 * aligned on a multiple of their size (i.e. 64-bit aligned on 64 bits, 32-bits
 * aligned on 32 bits, etc. Structs are always on a 64-bit boundary. This is
 * arbitrary and may change in the future for performance reasons. *)
let align array_size pos =
  let b = bytes_in array_size in
  let pos =
    if pos mod b = 0 then
      pos
    else
      pos + (bytes_in array_size - (pos mod bytes_in array_size))
  in
  pos

(* Helper *)
let fields_of_struct =
  List.map (fun (name, (t, _mut)) -> Option.must name, t)

(* A TQualified can either be a struct or an enum. Same for TAnonymous. *)
let is_enum env t =
  match t with
  | TQualified lid ->
      begin match LidMap.find lid env.layouts with
      | exception Not_found ->
          Warn.fatal_error "%a is not in the lid map!" plid lid
      | LEnum ->
          true
      | _ ->
          false
      end
  | TAnonymous (Enum _) -> true
  | _ -> false

let assert_lflat = function
  | LFlat layout -> layout
  | _ -> assert false

let is_lflat = function
  | LFlat _ -> true
  | _ -> false

(* The exact size as a number of bytes of any type. *)
let rec byte_size (env: env) (t: typ): int =
  match t with
  | TQualified lid ->
      begin match LidMap.find lid env.layouts with
      | LFlat layout -> layout.size
      | _ ->
          (* Must be atomic (builtin or enum). Defer to array_size_of. *)
          bytes_in (array_size_of env t)
      end
  | TAnonymous (Union cases) ->
      KList.reduce max (List.map (fun f -> (flat_layout env [ f ]).size) cases)
  | TAnonymous (Flat struct_fields) ->
      (flat_layout env (fields_of_struct struct_fields)).size
  | _ ->
      bytes_in (array_size_of env t)

(* Compute the offsets of each field of a struct. This function does NOT return
 * offsets for sub-fields. *)
and flat_layout env fields: flat_layout =
  let fields, size =
    List.fold_left (fun (fields, ofs) (fname, t) ->
      (* So far, we've laid out [fields], up to [ofs] bytes. *)
      match t with
      | (TQualified _ | TAnonymous _) when not (is_enum env t) ->
          (* Structs and unions align on a 64-byte boundary *)
          let size = byte_size env t in
          let ofs = align A64 ofs in
          (fname, ofs) :: fields, ofs + size
      | t ->
          (* All other elements align on their width. *)
          let s = array_size_of env t in
          let ofs = align s ofs in
          (fname, ofs) :: fields, ofs + bytes_in s
    ) ([], 0) fields
  in
  let fields = List.rev fields in
  { fields; size }

let field_offset env t f =
  match t with
  | TQualified lid ->
      List.assoc f (assert_lflat (LidMap.find lid env.layouts)).fields
  | TAnonymous (Union cases) ->
      assert (List.mem_assoc f cases);
      0
  | TAnonymous (Flat struct_fields) ->
      List.assoc f (flat_layout env (fields_of_struct struct_fields)).fields
  | _ ->
      failwith (KPrint.bsprintf "Not something we can field-offset: %a" ptyp t)

(* Laying out a type in an array cell occupies a multiple of a WASM array size. *)
let cell_size (env: env) (t: typ): int * array_size =
  let round_up size =
    let size = align A64 size in
    size / 8, A64
  in
  match t with
  | TQualified lid ->
      begin match LidMap.find lid env.layouts with
      | LFlat _ -> round_up (byte_size env t)
      | _ -> 1, array_size_of env t
      end
  | TAnonymous _ ->
      round_up (byte_size env t)
  | _ ->
      1, array_size_of env t

(* The size of any type, laid out in an array, in bytes. Morally, this is
 * [byte_size] with padding for alignment within an array. *)
let cell_size_b env t =
  let mult, base = cell_size env t in
  mult * bytes_in base

let populate env files =
  (* Assign integers to enums *)
  let env = List.fold_left (fun env (_, decls) ->
    List.fold_left (fun env decl ->
      match decl with
      | DType (_, _, _, Enum idents) ->
          KList.fold_lefti (fun i env ident ->
            assert (i < 256);
            { env with enums = LidMap.add ident i env.enums }
          ) env idents
      | _ ->
          env
    ) env decls
  ) env files in
  (* Fill in built-in layouts *)
  let env = List.fold_left (fun env (l, s, a_s) ->
    { env with layouts = LidMap.add l (LBuiltin (s, a_s)) env.layouts }
  ) env builtin_layouts in
  (* Compute the layouts for struct types that have an lid. *)
  let env = List.fold_left (fun env (_, decls) ->
    List.fold_left (fun env decl ->
      match decl with
      | DType (lid, _, _, Enum _) ->
          { env with layouts = LidMap.add lid LEnum env.layouts }
      | DType (lid, _, _, Flat fields) ->
          (* Need to pass in the layout of previous structs *)
          begin try
            let l = flat_layout env (fields_of_struct fields) in
            { env with layouts = LidMap.add lid (LFlat l) env.layouts }
          with e ->
            KPrint.beprintf "[AstToC♭] Can't compute the layout of %a:\n%s\n%s"
              PrintAst.plid lid (Printexc.to_string e)
              (if Options.debug "cflat" then Printexc.get_backtrace () ^ "\n" else "");
            env
          end
      | _ ->
          env
    ) env decls
  ) env files in
  env

let debug_env { layouts; enums; _ } =
  KPrint.bprintf "Struct layout:\n";
  LidMap.iter (fun lid l ->
    match l with
    | LFlat { size; fields } ->
        KPrint.bprintf "%a (size=%d, %d fields)\n" plid lid size (List.length fields);
        List.iter (fun (f, ofs) ->
          KPrint.bprintf "  +%d: %s\n" ofs f
        ) fields
    | LEnum ->
        KPrint.bprintf "%a (size=4, enum)\n" plid lid
    | LBuiltin _ ->
        KPrint.bprintf "%a (builtin)\n" plid lid
  ) layouts;
  KPrint.bprintf "Enum constant assignments:\n";
  LidMap.iter (fun lid d ->
    KPrint.bprintf "  %a = %d\n" plid lid d
  ) enums

(** When translating, we carry around the list of locals allocated so far within
 * the current function body, along with an environment (for the De Bruijn indices);
 * the i-th element in [binders] is De Bruijn variable [i]. When calling, say,
 * [mk_expr], the locals are returned (they monotonically grow) and the
 * environment is discarded.
 *
 * Note that this list is kept in reverse. *)
type locals = size list

(** An index in the locals table *)
type var = int

(** Bind a new Cflat variable. We always carry around all the allocated locals,
 * so they next local slot is just [List.length locals]. *)
let extend (env: env) (binder: binder) (locals: locals): locals * var * env =
  let v = List.length locals in
  size_of env binder.typ :: locals,
  v,
  { env with
    binders = List.length locals :: env.binders;
  }

(** Find a variable in the environment. *)
let find env v =
  List.nth env.binders v

(** A series of helpers. *)
let fold (f: locals -> 'a -> locals * 'b) (locals: locals) (xs: 'a list): locals * 'b list =
  let locals, ys = List.fold_left (fun (locals, acc) x ->
    let locals, y = f locals x in
    locals, y :: acc
  ) (locals, []) xs in
  locals, List.rev ys

let assert_var = function
  | CF.Var i -> i
  | _ -> invalid_arg "assert_var"

let assert_buf = function
  | TArray (t, _) | TBuf (t, _) -> t
  | _ -> invalid_arg "assert_buf"

let mk_add32 e1 e2 =
  CF.CallOp ((K.UInt32, K.Add), [ e1; e2 ])

let mk_mul32 e1 e2 =
  CF.CallOp ((K.UInt32, K.Mult), [ e1; e2 ])

let mk_lt32 e1 e2 =
  CF.CallOp ((K.UInt32, K.Lt), [ e1; e2 ])

let mk_uint32 i =
  CF.Constant (K.UInt32, string_of_int i)

let mk_minus1 e1 =
  CF.CallOp ((K.UInt32, K.Sub), [ e1; mk_uint32 1 ])

let mk_plus1 e1 =
  CF.CallOp ((K.UInt32, K.Add), [ e1; mk_uint32 1 ])

let mk_memcpy env locals dst src n =
  let b = Helpers.fresh_binder ~mut:true "i" (TInt K.UInt32) in
  let locals, v, _ = extend env b locals in
  locals, [
    CF.Assign (v, mk_uint32 0);
    CF.While (mk_lt32 (CF.Var v) n,
      let dst_ofs = CF.CallOp (K.(UInt32, Add), [ dst; CF.Var v ]) in
      let src_ofs = CF.CallOp (K.(UInt32, Add), [ src; CF.Var v ]) in
      CF.Sequence [
        CF.BufWrite (dst_ofs, 0, CF.BufRead (src_ofs, 0, A8), A8);
        CF.Assign (v, mk_plus1 (CF.Var v))
      ])]

let cflat_unit =
  CF.Constant (K.UInt32, "0xdeadbeef")

let cflat_any =
  CF.Constant (K.UInt32, "0xbadcaffe")

(* For any expression, compute a layout for it if it's not atomically writable.
 * Unlike flat_layout, this deals with any type, including anonymous union types
 * within tagged unions. *)
let layout_of env e =
  match e.node, e.typ with
  | _, TQualified lid ->
      begin match LidMap.find lid env.layouts with
      | LEnum | LBuiltin _ -> None
      | LFlat layout -> Some layout
      end
  | _, TAnonymous (Flat fields) ->
      Some (flat_layout env (fields_of_struct fields))
  | EFlat [ Some f, _ ], TAnonymous (Union cases) ->
      Some (flat_layout env [ f, List.assoc f cases ])
  | EFlat _, _ ->
      Warn.fatal_error "Cannot compute layout for: %a\n" pexpr e
  | _ ->
      None

(* Statically lay out a top-level constant into a bytes. This function is very
 * similar to the `write_at` underneath, except it is entirely syntax-driven. It
 * returns a string to be laid out, along with a list of expressions for
 * initializing sub-fields that refer to other global constant. *)
let write_static (env: env) (lid: lident) (e: expr): string * CFlat.expr list =
  let write_le dst ofs t const =
    let w = byte_size env t in
    for j = 0 to w - 1 do
      let shift = j * 8 in
      let j_byte_le = Z.((const asr shift) land (of_int 0xff)) in
      let c = char_of_int (Z.to_int j_byte_le) in
      Bytes.set dst (ofs + j) c
    done
  in
  let rec write_scalar dst ofs e =
    match e.node with
    | EBool b ->
        write_le dst ofs e.typ (if b then Z.one else Z.zero);
        []
    | EConstant ((Constant.UInt8 | Constant.UInt16 | Constant.UInt32 | Constant.UInt64), s) ->
        write_le dst ofs e.typ (Z.of_string s);
        []
    | EEnum lid ->
        write_le dst ofs e.typ (Z.of_int (LidMap.find lid env.enums));
        []
    | EFlat fields ->
        let layout = Option.must (layout_of env e) in
        KList.map_flatten (fun (fname, e) ->
          let fname = Option.must fname in
          let fofs = List.assoc fname layout.fields in
          write_scalar dst (ofs + fofs) e
        ) fields
    | EString s ->
        write_le dst ofs Helpers.uint32 (Z.of_int (Hashtbl.hash s));
        let name = GlobalNames.to_c_name env.names lid in
        [ CF.BufWrite (CF.GetGlobal name, ofs, CF.StringLiteral s, A32) ]
    | EQualified lid' ->
        let name = GlobalNames.to_c_name env.names lid in
        let name' = GlobalNames.to_c_name env.names lid' in
        (* This is to disable constant string initializers sharing -- we write a
         * dummy value. *)
        write_le dst ofs Helpers.uint32 (Z.of_int (Hashtbl.hash name'));
        [ CF.BufWrite (CF.GetGlobal name, ofs, CF.GetGlobal name', A32) ]
    | EApp ({ node = EQualified (["LowStar"; "Monotonic"; "Buffer"], "mnull"); _ }, _) ->
        write_le dst ofs Helpers.uint32 Z.zero;
        []
    | _ ->
        failwith (KPrint.bsprintf "Top-level constant contains unsupported value:\n\
          %a: %a" pexpr e ptyp e.typ)
  in
  (* Per the Low* restrictions, arrays may only appear at the top-level. *)
  match e.node with
  | EBufCreateL (_, es) ->
      let t = assert_buf e.typ in
      let cell_len = cell_size_b env t in
      let total_len = List.length es * cell_len in
      let buf = Bytes.create total_len in
      let es = List.mapi (fun i e -> write_scalar buf (i * cell_len) e) es in
      Bytes.to_string buf, List.flatten es
  | EBufCreate _ ->
      failwith "TODO: global constant array via bufcreate"
  | _ ->
      let t = e.typ in
      let buf = Bytes.create (byte_size env t) in
      let es = write_scalar buf 0 e in
      Bytes.to_string buf, es

let write_global env lid e =
  let s, es = write_static env lid e in
  { env with globals = LidMap.add lid s env.globals }, CF.StringLiteral s, es

(* Desugar an assignment into a series of possibly many assigments (e.g. struct
  * literal), or into a memcopy. We want to write [e] at address [dst] corrected
  * by an offset [ofs] in bytes. *)
let rec write_at (env: env)
  (locals: locals)
  (dst: CF.expr)
  (ofs: int)
  (e: expr): locals * CF.expr list
=
  (* KPrint.bprintf ">>> write_at: ofs=%d, e=%a\n" ofs pexpr e; *)
  let rec write_at locals (ofs, e) =
    (* KPrint.bprintf "  >>> write_at, inner: ofs=%d, e=%a\n" ofs pexpr e; *)
    match layout_of env e with
    | Some layout ->
        (* KPrint.bprintf "  >>> write_at: found a layout (size: %d)\n" layout.size; *)
        (* We are assigning something that's not a base type into an array. *)
        begin match e.node with
        | EFlat fields ->
            (* It's a literal. *)
            (* KPrint.bprintf "    >>> write_at: literal\n"; *)
            let locals, writes =
              fold (fun locals (fname, e) ->
                let fname = Option.must fname in
                let fofs = List.assoc fname layout.fields in
                (* Recursively write each field of the struct at its offset. *)
                write_at locals (ofs + fofs, e)
              ) locals fields
            in
            locals, List.flatten writes
        | _ ->
            (* KPrint.bprintf "    >>> write_at: memcpy\n"; *)
            (* If it's not a literal, it's got to be an address. Compute the
             * source, in bytes. *)
            let src = mk_addr env e in
            (* The size of the assignee, in bytes. *)
            let size = mk_uint32 (byte_size env e.typ) in
            (* Compute the destination, in bytes. *)
            let dst = mk_add32 dst (mk_uint32 ofs) in
            mk_memcpy env locals dst src size
        end
    | _ ->
        (* KPrint.bprintf "  >>> write_at: atomic\n"; *)
        (* Base case of an atomic type that can be written in one instruction
         * (machine integer, enum constant...) *)
        let s = array_size_of env e.typ in
        assert (ofs mod bytes_in s = 0);
        let e = mk_expr_no_locals env e in
        locals, [ CF.BufWrite (dst, ofs, e, s) ]
  in
  write_at locals (ofs, e)

and mk_expr_no_locals env e =
  let locals, e = mk_expr env [] e in
  assert (locals = []);
  e

(* Create an "lvalue" out of an expression. *)
and mk_addr env e =
  match e.node with
  | EBufRead (e1, e2) ->
      let s = cell_size_b env (assert_buf e1.typ) in
      let e1 = mk_expr_no_locals env e1 in
      let e2 = mk_expr_no_locals env e2 in
      CF.BufSub (e1, mk_mul32 e2 (mk_uint32 s), A8)
  | EField (e1, f) ->
      let ofs = field_offset env e1.typ f in
      let e1 = mk_addr env e1 in
      CF.BufSub (e1, mk_uint32 ofs, A8)
  | EQualified lid ->
      begin match e.typ with
      | TBuf _ -> ()
      | TQualified lid -> assert (is_lflat (LidMap.find lid env.layouts))
      | _ -> () end;
      let name = GlobalNames.to_c_name env.names lid in
      CF.GetGlobal name
  | EAbort _ ->
      mk_expr_no_locals env e
  | _ ->
      failwith (KPrint.bsprintf "can't take the addr of %a" pexpr e)

(** Assuming a base pointer, and an offset (simplified by [WasmSimplify] to be
 * either a variable, a constant, or a simple expression, e.g. [size - 1]), and
 * an element size sz, return a pair of a pointer and a possibly-zero offset (in
 * bytes) that corresponds to the given offset in the index. *)
and mk_offset env locals (base: CF.expr) (ofs: expr) (sz: int) =
  match ofs.node with
  | EConstant (_, c) ->
      (* TODO: overflow on 32-bit OCaml for string_of_int and subsequent
       * computations *)
      locals, base, int_of_string c * sz
  | _ ->
      let locals, ofs = mk_expr env locals ofs in
      (* The destination is the base pointer + the index * the size of an element. *)
      let dst = mk_add32 base (mk_mul32 ofs (mk_uint32 sz)) in
      locals, dst, 0

(** Translating a global declaration. *)
and mk_global (env: env) (lid: lident) (e: expr): env * CF.expr * CF.expr list =
  match e.node with
  | EBufCreate (Common.Eternal, _, _)
  | EBufCreateL (Common.Eternal, _)
  | EFlat _ ->
      write_global env lid e

  | EBufCreate _
  | EBufCreateL _ ->
      failwith "non-eternal CreateL in global position should've been ruled out by F* typing"

  | _ ->
      env, mk_expr_no_locals env e, []


(** The actual translation. Note that the environment is dropped, but that the
 * locals are chained through (state-passing style). *)
and mk_expr (env: env) (locals: locals) (e: expr): locals * CF.expr =
  match e.node with
  | EBound v ->
      locals, CF.Var (find env v)

  | EOpen _ ->
      invalid_arg "mk_expr (EOpen)"

  | EApp ({ node = EQualified (["Lib"; "Memzero0"],"memzero"); _ }, [ dst; len ]) ->
      let size = cell_size_b env dst.typ in
      let hd = with_type
        (TArrow (TBuf (TInt K.UInt8, false), TArrow (TInt K.UInt32, TArrow (TInt K.UInt32, TUnit))))
        (EQualified (["WasmSupport"], "memzero"))
      in
      mk_expr env locals (with_type e.typ (EApp (hd, [ dst; len; Helpers.mk_uint32 size ])))

  | EApp ({ node = EOp (o, w); _ }, es) ->
      let locals, es = fold (mk_expr env) locals es in
      locals, CF.CallOp ((w, o), es)

  | EApp ({ node = EQualified ident; _ }, es) ->
      let locals, es = fold (mk_expr env) locals es in
      locals, CF.CallFunc (GlobalNames.to_c_name env.names ident, es)

  | EApp _ ->
      failwith "unsupported application"

  | EConstant (w, lit) ->
      locals, CF.Constant (w, lit)

  | EEnum v ->
      locals, CF.Constant (K.UInt32, string_of_int (LidMap.find v env.enums))

  | EQualified v ->
      locals, CF.GetGlobal (GlobalNames.to_c_name env.names v)

  | EBufCreate (l, e_init, e_len) ->
      if not (e_init.node = EAny) then
        (* Should only happen for top-level declarations (see mk_global above). *)
        Warn.fatal_error "init node is not any but %a (see SimplifyWasm)\n" pexpr e_init;
      let locals, e_len = mk_expr env locals e_len in
      let mult, base_size = cell_size env (assert_buf e.typ) in
      if Options.debug "cflat" then
        KPrint.bprintf "Creating an array %a; one cell = %d * %s\n"
          ptyp e.typ mult (string_of_array_size base_size);
      locals, CF.BufCreate (l, mk_mul32 e_len (mk_uint32 mult), base_size)

  | EBufCreateL _ ->
      failwith "EBufCreateL in non-global position should've been desugared in SimplifyWasm"

  | EBufBlit _ | EBufFill _ ->
      failwith "EBufBlit / EBufFill should've been desugared in SimplifyWasm"

  | EBufRead (e1, e2) ->
      let s = array_size_of env (assert_buf e1.typ) in
      let locals, e1 = mk_expr env locals e1 in
      let locals, e1, offset = mk_offset env locals e1 e2 (bytes_in s) in
      locals, CF.BufRead (e1, offset, s)

  | EAddrOf ({ node = EQualified lid; _ }) ->
      begin match LidMap.find lid env.globals with
      | exception Not_found ->
          failwith (KPrint.bsprintf "address-of %a points to unresolved global" plid lid)
      | s ->
          locals, CFlat.StringLiteral s
      end

  | EAddrOf ({ node = EField (e1, f); _ }) ->
      (* This is the "address-of" operation from the paper. *)
      let ofs = List.assoc f (Option.must (layout_of env e1)).fields in
      let locals, e1 = mk_expr env locals (with_type (TBuf (e1.typ, true)) (EAddrOf e1)) in
      locals, mk_add32 e1 (mk_uint32 ofs)

  | EAddrOf ({ node = EBufRead (e1, e2); _ })
  | EBufSub (e1, e2) ->
      let mult, base_size = cell_size env (assert_buf e.typ) in
      let locals, e1 = mk_expr env locals e1 in
      let locals, e2 = mk_expr env locals e2 in
      locals, CF.BufSub (e1, mk_mul32 e2 (mk_uint32 mult), base_size)

  | EBufWrite ({ node = EBound v1; _ }, e2, e3) ->
      let v1 = CF.Var (find env v1) in
      let locals, dst, offset = mk_offset env locals v1 e2 (cell_size_b env e3.typ) in
      let locals, assignments = write_at env locals dst offset e3 in
      locals, CF.Sequence assignments

  | EBufWrite _ ->
      failwith (KPrint.bsprintf "buffer write improperly desugared: %a" pexpr e)

  | EBufFree _ ->
      failwith "TODO: implement manual memory management"

  | EBool b ->
      locals, CF.Constant (K.Bool, if b then "1" else "0")

  | ECast (e, TInt wt) ->
      let wf = match e.typ with TInt wf -> wf | _ -> failwith "non-int cast" in
      let locals, e = mk_expr env locals e in
      locals, CF.Cast (e, wf, wt)

  | ECast (e, TAny) ->
      let locals, e = mk_expr env locals e in
      locals, CF.Sequence [ e; cflat_any ]

  | EAny ->
      locals, cflat_any

  | ECast _ ->
      Warn.fatal_error "unsupported cast: %a" pexpr e

  | ELet (b, e1, e2) ->
      if e1.node = EAny then
        let locals, _, env = extend env b locals in
        let locals, e2 = mk_expr env locals e2 in
        locals, e2
      else
        let locals, e1 = mk_expr env locals e1 in
        let locals, v, env = extend env b locals in
        let locals, e2 = mk_expr env locals e2 in
        locals, CF.Sequence [
          CF.Assign (v, e1);
          e2
        ]

  | EIfThenElse (e1, e2, e3) ->
      let s2 = size_of env e2.typ in
      let s3 = size_of env e3.typ in
      assert (s2 = s3);
      let locals, e1 = mk_expr env locals e1 in
      let locals, e2 = mk_expr env locals e2 in
      let locals, e3 = mk_expr env locals e3 in
      locals, CF.IfThenElse (e1, e2, e3, s2)

  | EAbort s ->
      let s = match s with Some s -> s | None -> "<no message>" in
      locals, CF.Abort (CF.StringLiteral s)

  | EPushFrame ->
      locals, CF.Sequence []

  | EPopFrame ->
      locals, CF.Sequence []

  | ETuple _ | EMatch _ | ECons _ ->
      invalid_arg "should've been desugared before"

  | EComment (_, e, _) ->
      mk_expr env locals e

  | ESequence es ->
      let locals, es = fold (mk_expr env) locals es in
      locals, CF.Sequence es

  | EAssign (e1, e2) ->
      (* Assignment into a stack-allocated variable. For assignment into
       * addresses, EBufWrite is used. *)
      begin match e1.typ, e2.node with
      | TArray (_typ, _sizexp), _ ->
          invalid_arg "this should've been desugared by Simplify.Wasm into let + blit"
      | _ ->
          let locals, e1 = mk_expr env locals e1 in
          let locals, e2 = mk_expr env locals e2 in
          locals, CF.Assign (assert_var e1, e2)
      end

  | ESwitch (e, branches) ->
      let s = size_of env (snd (List.hd branches)).typ in
      let locals, e = mk_expr env locals e in
      let default, branches = List.partition (function (SWild, _) -> true | _ -> false) branches in
      let locals, default = match default with
        | [ SWild, e ] ->
            let locals, e = mk_expr env locals e in
            locals, Some e
        | [] ->
            locals, None
        | _ ->
            failwith "impossible"
      in
      let locals, branches = fold (fun locals (i, e) ->
        match i with
        | SEnum i ->
            let i = K.UInt32, string_of_int (LidMap.find i env.enums) in
            let locals, e = mk_expr env locals e in
            locals, (i, e)
        | SConstant i ->
            let locals, e = mk_expr env locals e in
            locals, (i, e)
        | SWild ->
            failwith "impossible"
      ) locals branches in
      locals, CF.Switch (e, branches, default, s)

  | EFor (b, e1, e2, e3, e4) ->
      let locals, e1 = mk_expr env locals e1 in
      let locals, v, env = extend env b locals in
      let locals, e2 = mk_expr env locals e2 in
      let locals, e3 = mk_expr env locals e3 in
      let locals, e4 = mk_expr env locals e4 in
      locals, CF.Sequence [
        CF.Assign (v, e1);
        CF.While (e2, CF.Sequence [ e4; e3 ])]

  | EWhile (e1, e2) ->
      let locals, e1 = mk_expr env locals e1 in
      let locals, e2 = mk_expr env locals e2 in
      locals, CF.While (e1, e2)

  | EString s ->
      locals, CF.StringLiteral s

  | EUnit ->
      locals, cflat_unit

  | EStandaloneComment _ ->
      locals, cflat_unit

  | EField (e1, f) ->
      (* e1 is a structure expression, and structures are allocated in memory. *)
      let s = array_size_of env e.typ in
      let addr = mk_addr env e1 in
      let ofs = field_offset env e1.typ f in
      assert (ofs mod bytes_in s = 0);
      locals, CF.BufRead (addr, ofs, s)

  | EOp _ ->
      failwith "standalone application"

  | EFlat _ ->
      failwith "todo eflat"

  | EReturn _ ->
      invalid_arg "return shouldnt've been inserted"

  | EBreak ->
      failwith "todo break"

  | ETApp _ ->
      invalid_arg "no type apps"

  | EFun _ ->
      invalid_arg "funs should've been substituted"

  | EAddrOf _ ->
      Warn.fatal_error "address-of should've been resolved: %a" pexpr e

  | EIgnore e ->
      let s = size_of env e.typ in
      let locals, e = mk_expr env locals e in
      locals, CF.Ignore (e, s)


(* See digression for [dup32] in CFlatToWasm *)
let scratch_locals =
  [ I64; I64; I32; I32 ]

let mk_decl env (d: decl): env * CF.decl option =
  match d with
  | DFunction (_, flags, n, ret, name, args, body) ->
      assert (n = 0);
      let public = not (List.exists ((=) Common.Private) flags) in
      let locals, env = List.fold_left (fun (locals, env) b ->
        let locals, _, env = extend env b locals in
        locals, env
      ) ([], env) args in
      let locals = List.rev_append scratch_locals locals in
      let locals, body = mk_expr env locals body in
      let ret = [ size_of env ret ] in
      let locals = List.rev locals in
      let args, locals = KList.split (List.length args) locals in
      let name = GlobalNames.to_c_name env.names name in
      env, Some CF.(Function { name; args; ret; locals; body; public })

  | DType _ ->
      (* Not translating type declarations. *)
      env, None

  | DGlobal (flags, name, n, typ, body) ->
      assert (n = 0);
      let public = not (List.exists ((=) Common.Private) flags) in
      let size =
        match body.node with
        | EFlat _ -> I32
        | _ -> size_of env typ
      in
      if size = I64 then begin
        Warn.(maybe_fatal_error ("", NotWasmCompatible (name, "I64 constant")));
        env, None
      end else
        let env, body, post_init = mk_global env name body in
        let name = GlobalNames.to_c_name env.names name in
        env, Some (CF.Global (name, size, body, post_init, public))

  | DExternal (_, _, lid, t, _) ->
      let name = GlobalNames.to_c_name env.names lid in
      match t with
      | TArrow _ ->
          let ret, args = Helpers.flatten_arrow t in
          let ret = [ size_of env ret ] in
          let args = List.map (size_of env) args in
          if (List.hd ret = I64 || List.mem I64 args) && not (CFlatToWasm.is_primitive name) then begin
            Warn.(maybe_fatal_error ("", NotWasmCompatible (lid, "functions \
              implemented natively in JS (because they're assumed) cannot take or \
              return I64")));
            env, None
          end else
            env, Some (CF.ExternalFunction (name, args, ret))
      | _ ->
          env, Some (CF.ExternalGlobal (name, size_of env t))

(* Definitions to be skipped because they have a built-in compilation scheme. *)
let skip (lid: lident) =
  let skip = [[ "LowStar"; "Monotonic"; "Buffer" ], "mnull"] in
  List.mem lid skip

let mk_module env decls =
  let env, decls = List.fold_left (fun (env, decls) d ->
    try
      if skip (lid_of_decl d) then
        env, decls
      else begin
        flush stdout; flush stderr;
        let env, d = mk_decl env d in
        match d with
        | None -> env, decls
        | Some d -> env, d :: decls
      end
    with e ->
      flush stdout;
      flush stderr;
      (* Remove when everything starts working *)
      KPrint.beprintf "[AstToC♭] Couldn't translate %s%a%s:\n%s\n%s"
        Ansi.underline PrintAst.plid (lid_of_decl d) Ansi.reset (Printexc.to_string e)
        (if Options.debug "backtraces" then Printexc.get_backtrace () ^ "\n" else "");
      env, decls
  ) (env, []) decls in
  env, List.rev decls

let mk_files files names =
  let env = populate (empty names) files in
  if Options.debug "cflat" then
    debug_env env;
  let _, modules = List.fold_left (fun (env, ms) (name, decls) ->
    let env, decls = mk_module env decls in
    env, (name, decls) :: ms
  ) (env, []) files in
  List.rev modules

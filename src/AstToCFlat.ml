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
  structs: layout LidMap.t;
    (** Pre-computed layouts for struct types. *)
}

and layout = {
  size: int;
    (** In bytes *)
  fields: (string * offset) list;
    (** Any struct must be laid out on a word boundary (64-bit). Then, fields
     * can be always accessed using the most efficient offset computation. *)
}

and offset = int
  (** In byte *)

let empty = {
  binders = [];
  enums = LidMap.empty;
  structs = LidMap.empty;
}

(** Layouts and sizes. *)

(** The size of a type that fits in one WASM value. *)
let size_of (t: typ): size =
  match t with
  | TInt w ->
      size_of_width w
  | TArray _ | TBuf _ ->
      I32
  | TBool | TUnit ->
      I32
  | TAnonymous (Enum _) ->
      I32
  | _ ->
      failwith (KPrint.bsprintf "size_of: this case should've been eliminated: %a" ptyp t)

(* The size of a type that fits in one WASM array cell. *)
let array_size_of (t: typ): array_size =
  match t with
  | TInt w ->
      array_size_of_width w
  | TArray _ | TBuf _ ->
      A32
  | TBool | TUnit ->
      A32 (* Todo: pack these more efficiently?! *)
  | TAnonymous (Enum _) ->
      A32
  | _ ->
      failwith (KPrint.bsprintf "size_of: this case should've been eliminated: %a" ptyp t)

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

(* The exact size as a number of bytes of any type. *)
let rec byte_size (env: env) (t: typ): int =
  match t with
  | TQualified lid ->
      begin try
        (LidMap.find lid env.structs).size
      with Not_found ->
        failwith (KPrint.bsprintf "Can't compute the byte size of %a" plid lid)
      end
  | TAnonymous (Union cases) ->
      KList.reduce max (List.map (fun f -> (layout env [ f ]).size) cases)
  | TAnonymous (Flat struct_fields) ->
      (layout env (fields_of_struct struct_fields)).size
  | _ ->
      bytes_in (array_size_of t)

(* Compute the offsets of each field of a struct. This function does NOT return
 * offsets for sub-fields. *)
and layout env fields: layout =
  let fields, size =
    List.fold_left (fun (fields, ofs) (fname, t) ->
      (* So far, we've laid out [fields], up to [ofs] bytes. *)
      match t with
      | TQualified _
      | TAnonymous _ ->
          (* Structs and unions align on a 64-byte boundary *)
          let size = byte_size env t in
          let ofs = align A64 ofs in
          (fname, ofs) :: fields, ofs + size
      | t ->
          (* All other elements align on their width. *)
          let s = array_size_of t in
          let ofs = align s ofs in
          (fname, ofs) :: fields, ofs + bytes_in s
    ) ([], 0) fields
  in
  let fields = List.rev fields in
  { fields; size }

let field_offset env t f =
  match t with
  | TQualified lid ->
      List.assoc f (LidMap.find lid env.structs).fields
  | TAnonymous (Union cases) ->
      assert (List.mem_assoc f cases);
      0
  | TAnonymous (Flat struct_fields) ->
      List.assoc f (layout env (fields_of_struct struct_fields)).fields
  | _ ->
      failwith (KPrint.bsprintf "Not something we can field-offset: %a" ptyp t)

(* Layout a type in an array cell occupies a multiple of a WASM array size. *)
let cell_size (env: env) (t: typ): int * array_size =
  let round_up size =
    let size = align A64 size in
    size / 8, A64
  in
  match t with
  | TQualified _ | TAnonymous _ ->
      round_up (byte_size env t)
  | _ ->
      1, array_size_of t

let cell_size_b env t =
  let mult, base = cell_size env t in
  mult * bytes_in base

let populate env files =
  (* Assign integers to enums *)
  let env = List.fold_left (fun env (_, decls) ->
    List.fold_left (fun env decl ->
      match decl with
      | DType (_, _, _, Enum idents, _) ->
          KList.fold_lefti (fun i env ident ->
            { env with enums = LidMap.add ident i env.enums }
          ) env idents
      | _ ->
          env
    ) env decls
  ) env files in
  (* Compute the layouts for structs that have an lid. The rest will be (for
   * now) computed on demand. *)
  let env = List.fold_left (fun env (_, decls) ->
    List.fold_left (fun env decl ->
      match decl with
      | DType (lid, _, _, Flat fields, _) ->
          (* Need to pass in the layout of previous structs *)
          begin try
            let l = layout env (fields_of_struct fields) in
            { env with structs = LidMap.add lid l env.structs }
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

let debug_env { structs; enums; _ } =
  KPrint.bprintf "Struct layout:\n";
  LidMap.iter (fun lid { size; fields } ->
    KPrint.bprintf "%a (size=%d, %d fields)\n" plid lid size (List.length fields);
    List.iter (fun (f, ofs) ->
      KPrint.bprintf "  +%d: %s\n" ofs f
    ) fields
  ) structs;
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
  size_of binder.typ :: locals,
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
  | TArray (t, _) | TBuf t -> t
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

let mk_memcpy env locals dst src n =
  let b = Helpers.fresh_binder ~mut:true "i" (TInt K.UInt32) in
  let locals, v, _ = extend env b locals in
  locals, [
    CF.Assign (v, mk_uint32 0);
    CF.While (mk_lt32 (CF.Var v) n,
      CF.Sequence [
        CF.BufWrite (dst, (CF.Var v), CF.BufRead (src, (CF.Var v), A8), A8);
        CF.Assign (v, mk_minus1 (CF.Var v))
      ])]

(* Desugar an array assignment into a series of possibly many assigments (e.g.
 * struct literal), or into a memcopy *)
let rec write_at (env: env)
  (locals: locals)
  (arr: CF.expr)
  (base_ofs: CF.expr)
  (ofs: int)
  (e: expr): locals * CF.expr list
=
  let rec write_at locals (ofs, e) =
    match e.typ with
    | TQualified lid ->
        let layout = LidMap.find lid env.structs in
        begin match e.node with
        | EFlat fields ->
            let locals, writes =
              fold (fun locals (fname, e) ->
                let fname = Option.must fname in
                let fofs = List.assoc fname layout.fields in
                write_at locals (ofs + fofs, e)
              ) locals fields
            in
            locals, List.flatten writes
        | _ ->
            let addr = mk_addr env e in
            let size = byte_size env e.typ in
            mk_memcpy env locals (mk_add32 base_ofs (mk_uint32 ofs)) addr (mk_uint32 size)
        end
    | _ ->
        let s = array_size_of e.typ in
        assert (ofs mod bytes_in s = 0);
        let ofs = ofs / bytes_in s in
        let e = mk_expr_no_locals env e in
        locals, [ CF.BufWrite (arr, mk_add32 base_ofs (mk_uint32 ofs), e, s) ]
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
  | _ ->
      failwith (KPrint.bsprintf "can't take the addr of %a" pexpr e)

(** The actual translation. Note that the environment is dropped, but that the
 * locals are chained through (state-passing style). *)
and mk_expr (env: env) (locals: locals) (e: expr): locals * CF.expr =
  match e.node with
  | EBound v ->
      locals, CF.Var (find env v)

  | EOpen _ ->
      invalid_arg "mk_expr (EOpen)"

  | EApp ({ node = EOp (o, w); _ }, es) ->
      let locals, es = fold (mk_expr env) locals es in
      locals, CF.CallOp ((w, o), es)

  | EApp ({ node = EQualified ident; _ }, es) ->
      let locals, es = fold (mk_expr env) locals es in
      locals, CF.CallFunc (Idents.string_of_lident ident, es)

  | EApp _ ->
      failwith "unsupported application"

  | EConstant (w, lit) ->
      locals, CF.Constant (w, lit)

  | EEnum v ->
      locals, CF.Constant (K.UInt32, string_of_int (LidMap.find v env.enums))

  | EQualified v ->
      locals, CF.GetGlobal (Idents.string_of_lident v)

  | EBufCreate (l, e_init, e_len) ->
      assert (e_init.node = EAny);
      let locals, e_len = mk_expr env locals e_len in
      let mult, base_size = cell_size env (assert_buf e.typ) in
      if Options.debug "cflat" then
        KPrint.bprintf "Creating an array %a; one cell = %d * %s\n"
          ptyp e.typ mult (string_of_array_size base_size);
      locals, CF.BufCreate (l, mk_mul32 e_len (mk_uint32 mult), base_size)

  | EBufCreateL _ | EBufBlit _ | EBufFill _ ->
      invalid_arg "this should've been desugared in Simplify.wasm"

  | EBufRead (e1, e2) ->
      let s = array_size_of (assert_buf e1.typ) in
      let locals, e1 = mk_expr env locals e1 in
      let locals, e2 = mk_expr env locals e2 in
      locals, CF.BufRead (e1, e2, s)

  | EBufSub (e1, e2) ->
      let s = array_size_of (assert_buf e1.typ) in
      let locals, e1 = mk_expr env locals e1 in
      let locals, e2 = mk_expr env locals e2 in
      locals, CF.BufSub (e1, e2, s)

  | EBufWrite ({ node = EBound v1; _ }, e2, e3) ->
      (* e2 has been simplified by [WasmSimplify] to be either a variable, a
       * constant, or simple expressions (e.g. [size - 1]). *)
      let v1 = CF.Var (find env v1) in
      let e2 = mk_expr_no_locals env e2 in
      let locals, assignments = write_at env locals v1 e2 0 e3 in
      locals, CF.Sequence assignments

  | EBufWrite _ ->
      failwith (KPrint.bsprintf "buffer write improperly desugared: %a" pexpr e)

  | EBool b ->
      locals, CF.Constant (K.Bool, if b then "1" else "0")

  | ECast (e, TInt wt) ->
      let wf = match e.typ with TInt wf -> wf | _ -> failwith "non-int cast" in
      let locals, e = mk_expr env locals e in
      locals, CF.Cast (e, wf, wt)

  | ECast _ ->
      failwith "unsupported cast"

  | EAny ->
      failwith "not supported EAny"

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
      let s2 = size_of e2.typ in
      let s3 = size_of e3.typ in
      assert (s2 = s3);
      let locals, e1 = mk_expr env locals e1 in
      let locals, e2 = mk_expr env locals e2 in
      let locals, e3 = mk_expr env locals e3 in
      locals, CF.IfThenElse (e1, e2, e3, s2)

  | EAbort _ ->
      locals, CF.Abort

  | EPushFrame ->
      locals, CF.PushFrame

  | EPopFrame ->
      locals, CF.PopFrame

  | ETuple _ | EMatch _ | ECons _ ->
      invalid_arg "should've been desugared before"

  | EComment (_, e, _) ->
      mk_expr env locals e

  | ESequence es ->
      let locals, es = fold (mk_expr env) locals es in
      locals, CF.Sequence es

  | EAssign (e1, e2) ->
      begin match e1.typ, e2.node with
      | TArray (_typ, _sizexp), (EBufCreate _ | EBufCreateL _) ->
          invalid_arg "this should've been desugared by Simplify.Wasm into let + blit"
      | _ ->
          let locals, e1 = mk_expr env locals e1 in
          let locals, e2 = mk_expr env locals e2 in
          locals, CF.Assign (assert_var e1, e2)
      end

  | ESwitch (e, branches) ->
      let locals, e = mk_expr env locals e in
      let locals, branches = fold (fun locals (i, e) ->
        let i = CF.Constant (K.UInt32, string_of_int (LidMap.find i env.enums)) in
        let locals, e = mk_expr env locals e in
        locals, (i, e)
      ) locals branches in
      locals, CF.Switch (e, branches)

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
      locals, CF.Constant (K.UInt32, "0xdeadbeef")

  | EField (e1, f) ->
      (* e1 is a structure expression, and structures are allocated in memory. *)
      let s = array_size_of e.typ in
      let addr = mk_addr env e1 in
      let ofs = field_offset env e1.typ f in
      assert (ofs mod bytes_in s = 0);
      let ofs = ofs / bytes_in s in
      locals, CF.BufRead (addr, mk_uint32 ofs, s)

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
      invalid_arg "address-of should've been resolved"

  | EIgnore _ ->
      failwith "TODO"


(* See digression for [dup32] in CFlatToWasm *)
let scratch_locals =
  [ I64; I64; I32; I32 ]

let mk_decl env (d: decl): CF.decl option =
  match d with
  | DFunction (_, flags, n, ret, name, args, body, _src_info) ->
      assert (n = 0);
      let public = not (List.exists ((=) Common.Private) flags) in
      let locals, env = List.fold_left (fun (locals, env) b ->
        let locals, _, env = extend env b locals in
        locals, env
      ) ([], env) args in
      let locals = List.rev_append scratch_locals locals in
      let locals, body = mk_expr env locals body in
      let ret = [ size_of ret ] in
      let locals = List.rev locals in
      let args, locals = KList.split (List.length args) locals in
      let name = Idents.string_of_lident name in
      Some CF.(Function { name; args; ret; locals; body; public })

  | DType _ | DTypeMutual _ ->
      (* Not translating type declarations. *)
      None

  | DGlobal (flags, name, typ, body) ->
      let public = not (List.exists ((=) Common.Private) flags) in
      let size = size_of typ in
      let body = mk_expr_no_locals env body in
      let name = Idents.string_of_lident name in
      Some (CF.Global (name, size, body, public))

  | DExternal (_, lid, t, _binders) ->
      let name = Idents.string_of_lident lid in
      match t with
      | TArrow _ ->
          let ret, args = Helpers.flatten_arrow t in
          let ret = [ size_of ret ] in
          let args = List.map size_of args in
          Some (CF.ExternalFunction (name, args, ret))
      | _ ->
          Some (CF.ExternalGlobal (name, size_of t))

let mk_module env (name, decls) =
  name, KList.filter_map (fun d ->
    try
      mk_decl env d
    with e ->
      (* Remove when everything starts working *)
      KPrint.beprintf "[AstToC♭] Couldn't translate %a:\n%s\n%s"
        PrintAst.plid (lid_of_decl d) (Printexc.to_string e)
        (if Options.debug "cflat" then Printexc.get_backtrace () ^ "\n" else "");
      None
  ) decls

let mk_files files =
  let env = populate empty files in
  if Options.debug "cflat" then
    debug_env env;
  List.map (mk_module env) files

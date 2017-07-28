(** Going from CStar to CFlat *)

module CF = CFlat
module K = Constant
module LidMap = Idents.LidMap
module StringMap = Map.Make(String)

(** Sizes *)

open CFlat.Sizes
open Ast
open PrintAst.Ops

(** We know how much space is needed to represent each C* type. *)
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
  | TAnonymous (Variant _ | Abbrev _)
  | TZ | TBound _ | TTuple _ | TArrow _ | TQualified _ | TApp _ ->
      failwith (KPrint.bsprintf "size_of: this case should've been eliminated: %a" ptyp t)
  | TAnonymous _ | TAny as t ->
      failwith (KPrint.bsprintf "not implemented: size_of %a" ptyp t)

let max_size s1 s2 =
  match s1, s2 with
  | I32, I32 -> I32
  | _ -> I64

let array_size_of (t: typ): array_size =
  match t with
  | TInt w ->
      array_size_of_width w
  | TArray _ | TBuf _ ->
      A32
  | TBool | TUnit ->
      failwith "todo: packed arrays of bools/units?!"
  | TAnonymous (Enum _) ->
      A32
  | TAnonymous (Variant _ | Abbrev _)
  | TZ | TBound _ | TTuple _ | TArrow _ | TQualified _ | TApp _ ->
      failwith (KPrint.bsprintf "size_of: this case should've been eliminated: %a" ptyp t)
  | TAnonymous _ | TAny as t ->
      failwith (KPrint.bsprintf "not implemented: array_size_of %a" ptyp t)


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

(** Layouts.
 *
 * Filling in the initial environment with struct layout, and an assignment of
 * enum constants to integers. *)

let struct_size env lid =
  (LidMap.find lid env.structs).size

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

let fields_of_struct =
  List.map (fun (name, (t, _mut)) -> Option.must name, t)

(* Compute the offsets of each field of a struct. This function does NOT return
 * offsets for sub-fields. *)
let rec layout env fields: layout =
  let fields, size =
    List.fold_left (fun (fields, ofs) (fname, t) ->
      (* So far, we've laid out [fields], up to [ofs] bytes. *)
      match t with
      | TQualified lid ->
          if not (LidMap.mem lid env.structs) then begin
            KPrint.bprintf "Cannot layout sub-field %s of type %a... skipping\n"
              fname ptyp t;
            fields, ofs
          end else
            (* A previously-defined, previously laid-out struct. *)
            let ofs = align A64 ofs in
            (fname, ofs) :: fields, ofs + struct_size env lid
      | TUnit ->
          KPrint.bprintf "Skipping sub-field %s of type unit\n" fname;
          fields, ofs
      | TAnonymous (Union cases) ->
          let ofs = align A64 ofs in
          let max_size = KList.reduce max
            (List.map (fun f -> (layout env [ f ]).size) cases)
          in
          (fname, ofs) :: fields, ofs + max_size
      | TAnonymous (Flat struct_fields) ->
          let ofs = align A64 ofs in
          let size = (layout env (fields_of_struct struct_fields)).size in
          (fname, ofs) :: fields, ofs + size
      | t ->
          let s = array_size_of t in
          let ofs = align s ofs in
          (fname, ofs) :: fields, ofs + bytes_in s
    ) ([], 0) fields
  in
  let fields = List.rev fields in
  { fields; size }

let populate env files =
  (* Assign integers to enums *)
  let env = List.fold_left (fun env (_, decls) ->
    List.fold_left (fun env decl ->
      match decl with
      | DType (_, _, Enum idents) ->
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
      | DType (lid, _, Flat fields) ->
          (* Need to pass in the layout of previous structs *)
          let l = layout env (fields_of_struct fields) in
          { env with structs = LidMap.add lid l env.structs }
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

(** A helpful combinator. *)
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

let mk_int32 i =
  CF.Constant (K.UInt32, string_of_int i)

(* Desugar an array assignment into a series of possibly many assigments (e.g.
 * struct literal), or into a memcopy *)
let rec write_at (env: env) (arr: CF.expr) (base_ofs: CF.expr) (ofs: int) (e: expr): CF.expr list =
  let rec write_at ofs e =
    match e.typ with
    | TQualified lid ->
        let layout = LidMap.find lid env.structs in
        begin match e.node with
        | EFlat fields ->
            KList.map_flatten (fun (fname, e) ->
              let fname = Option.must fname in
              let fofs = List.assoc fname layout.fields in
              write_at (ofs + fofs) e
            ) fields
        | _ ->
            failwith (KPrint.bsprintf "todo: layout %a\n" pexpr e)
        end
    | _ ->
        let s = array_size_of e.typ in
        let e = mk_expr_no_locals env e in
        [ CF.BufWrite (arr, mk_add32 base_ofs (mk_int32 ofs), e, s) ]
  in
  write_at ofs e

and mk_expr_no_locals env e =
  let locals, e = mk_expr env [] e in
  assert (locals = []);
  e

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
      locals, CF.BufCreate (l, e_len, array_size_of (assert_buf e.typ))

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
      let assignments = write_at env v1 e2 0 e3 in
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
      locals, CF.Constant (K.UInt32, "0")

  | EOp _ ->
      failwith "standalone application"

  | EFlat _ | EField _ ->
      failwith "todo eflat"

  | EReturn _ ->
      invalid_arg "return shouldnt've been inserted"

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
  | DFunction (_, flags, n, ret, name, args, body) ->
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

  | DType _ ->
      (* Not translating type declarations. *)
      None

  | DGlobal (flags, name, typ, body) ->
      let public = not (List.exists ((=) Common.Private) flags) in
      let size = size_of typ in
      let locals, body = mk_expr env [] body in
      let name = Idents.string_of_lident name in
      if locals = [] then
        Some (CF.Global (name, size, body, public))
      else
        failwith "global generates let-bindings"

  | _ ->
      failwith ("not implemented (decl); got: " ^ show_decl d)

let mk_module env (name, decls) =
  name, KList.filter_map (fun d ->
    try
      mk_decl env d
    with e ->
      (* Remove when everything starts working *)
      KPrint.beprintf "[AstToC♭] Couldn't translate %a:\n%s\n%s\n"
        PrintAst.plid (lid_of_decl d) (Printexc.to_string e)
        (Printexc.get_backtrace ());
      None
  ) decls

let mk_files files =
  let env = populate empty files in
  if Options.debug "cflat" then
    debug_env env;
  List.map (mk_module env) files

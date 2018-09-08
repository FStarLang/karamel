(* Wasm-specific transformations that we perform now **************************)

open Ast
open Helpers
open DeBruijn

let check_buffer_size =
  with_type (TArrow (TInt K.UInt32, TUnit)) (EQualified ([ "WasmSupport" ], "check_buffer_size"))


let hoist_reads_and_writes = object(self)
  inherit [_] map

  method! visit_EBufWrite env e1 e2 e3 =
    (* TODO: separate the two pattern-matches because EConstant for e2 is still
     * good regardless of what e1 is *)
    match e1.node, e2.node with
    | (EOpen _ | EBound _), EConstant _ ->
        EBufWrite (e1, e2, e3)
    | _ ->
        let b_e1, body_e1, ref_e1 = mk_named_binding "dst" e1.typ e1.node in
        let b_e2, body_e2, ref_e2 = mk_named_binding "ofs" e2.typ e2.node in
        ELet (b_e1, body_e1, close_binder b_e1 (with_unit (
        ELet (b_e2, body_e2, close_binder b_e2 (with_unit (
          EBufWrite (ref_e1, ref_e2, self#visit_expr env e3)))))))

  method! visit_EBufRead (_, t) e1 e2 =
    match e1.node, e2.node with
    | (EOpen _ | EBound _), EConstant _ ->
        EBufRead (e1, e2)
    | _ ->
        let b_e1, body_e1, ref_e1 = mk_named_binding "src" e1.typ e1.node in
        let b_e2, body_e2, ref_e2 = mk_named_binding "ofs" e2.typ e2.node in
        ELet (b_e1, body_e1, close_binder b_e1 (with_type t (
        ELet (b_e2, body_e2, close_binder b_e2 (with_type t (
          EBufRead (ref_e1, ref_e2)))))))

end

let remove_buffer_ops = object(self)
  inherit [_] map as super

  (* The relatively simple [bufcreate init size] is rewritten, because no
   * initial value for buffers in CFlat:
   *
   *   let s = size in
   *   let b = bufcreate s in
   *   b[0] = init;
   *   s--;
   *   while (s > 0)
   *     b[s] = b[0];
   *     s--;
   *   b
   * *)
  method! visit_EBufCreate (_, t) lifetime init size =
    match init.node with
    | EAny ->
        EBufCreate (lifetime, init, size)
    | _ ->
        let b_size, body_size, ref_size = mk_named_binding "size" size.typ size.node in
        let b_size = mark_mut b_size in
        (* Leaving the size inline because it's needed for the buffer hoisting
         * phase; also, the size ought to be pure, guaranteed by F*. *)
        let b_buf, body_buf, ref_buf = mk_named_binding "buf" t (EBufCreate (lifetime, any, size)) in
        let with_t = with_type t in
        match size.node with
        | EConstant (_, "1") ->
            ELet (b_buf, body_buf, close_binder b_buf (with_t (
              ESequence [ with_unit (
                EBufWrite (ref_buf, zerou32, init));
                ref_buf ])))
        | _ ->
            ELet (b_size, body_size, close_binder b_size (with_t (
              ESequence [ with_unit (
                EApp (check_buffer_size, [ ref_size ])); with_unit (
                ELet (b_buf, body_buf, close_binder b_buf (with_t (
                  ESequence [ with_unit (
                    EBufWrite (ref_buf, zerou32, init)); with_unit (
                    EAssign (ref_size, mk_minus_one ref_size)); with_unit (
                    EWhile (
                      mk_gt_zero ref_size, with_unit (
                      ESequence [ with_unit (
                        EBufWrite (
                          ref_buf,
                          ref_size,
                          with_t (EBufRead (ref_buf, zerou32)))); with_unit (
                        EAssign (ref_size, mk_minus_one ref_size))])));
                  ref_buf]))))])))

  method! visit_EBufCreateL (_, t) lifetime es =
    let es = List.map (self#visit_expr_w ()) es in
    let size = mk_uint32 (List.length es) in
    let with_t = with_type t in
    let b_buf, body_buf, ref_buf = mk_named_binding "buf" t (EBufCreate (lifetime, any, size)) in
    (* JP: DeBruijn.lift 1 e here? *)
    let assignments = List.mapi (fun i e -> with_unit (EBufWrite (ref_buf, mk_uint32 i, e))) es in
    ELet (b_buf, body_buf, close_binder b_buf (with_t (
      ESequence (assignments @ [ ref_buf ]))))

  method! visit_EBufBlit _ src_buf src_ofs dst_buf dst_ofs len =
    mk_bufblit src_buf src_ofs dst_buf dst_ofs len

  method! visit_DGlobal env flags lid n t e =
    match e.node with
    | EBufCreate _ | EBufCreateL _ ->
        DGlobal (flags, lid, n, t, e)
    | _ ->
        super#visit_DGlobal env flags lid n t e

end

(* No partial applications ****************************************************)

(* TODO: figure out if we want to ignore the other cases for performance
 * reasons. *)
let eta_expand = object
  inherit [_] map

  method! visit_DGlobal () flags name n t body =
    assert (n = 0);
    (* TODO: eta-expand partially applied functions *)
    match t with
    | TArrow _ ->
        let tret, targs = flatten_arrow t in
        let n = List.length targs in
        let binders, args = List.split (List.mapi (fun i t ->
          with_type t { name = Printf.sprintf "x%d" i; mut = false; mark = ref 0; meta = None; atom = Atom.fresh () },
          { node = EBound (n - i - 1); typ = t }
        ) targs) in
        let body = { node = EApp (body, args); typ = tret } in
        DFunction (None, flags, 0, tret, name, binders, body)
    | _ ->
        DGlobal (flags, name, n, t, body)
end

let simplify1 (files: file list): file list =
  let files = hoist_reads_and_writes#visit_files () files in
  files

let simplify2 (files: file list): file list =
  let files = remove_buffer_ops#visit_files () files in
  (* Note: this is not added at the C level because function pointers are ok,
   * and the C printer is capable of dealing with a global variable that is
   * actually a function. Also not doing this at the C level because this
   * currently breaks some use-cases, such as:
   *   let f x = if x then g1 else g2
   *   let g = f true
   *   let _ =
   *     g foo
   * but this is only because we're not tracking the natural arity of a
   * function, just like OCaml does for the natural arity of a function at the C
   * ABI level.
   * See https://github.com/FStarLang/kremlin/issues/52 for reference.
   * *)
  let files = eta_expand#visit_files () files in
  files

(* Wasm-specific transformations that we perform now **************************)

open Ast
open Helpers
open DeBruijn

let remove_buffer_ops = object
  inherit [unit] map

  (* The relatively simple:
   *
   *   bufcreate init size
   *
   * is rewritten to:
   *
   *   let i = init in
   *   let s = size in
   *   let b = bufcreate i s in
   *   while (s > 0)
   *     b[s] = i;
   *     i--;
   *   b
   * *)
  method ebufcreate () t lifetime init size =
    let b_init, body_init, ref_init = mk_named_binding "init" init.typ init.node in
    let b_size, body_size, ref_size = mk_named_binding "size" size.typ size.node in
    let b_size = mark_mut b_size in
    let b_buf, body_buf, ref_buf = mk_named_binding "buf" t (EBufCreate (lifetime, any, ref_size)) in
    let with_t = with_type t in
    ELet (b_init, body_init, close_binder b_init (with_t (
    ELet (b_size, body_size, close_binder b_size (with_t (
    ELet (b_buf, body_buf, close_binder b_buf (with_t (
      ESequence [ with_unit (
        EWhile (
          mk_gt_zero ref_size, with_unit (
          ESequence [ with_unit (
            EBufWrite (ref_buf, mk_minus_one ref_size, ref_init)); with_unit (
            EAssign (ref_size, mk_minus_one ref_size))])));
      ref_buf])))))))))

  method ebufblit () t src_buf src_ofs dst_buf dst_ofs len =
    let with_t = with_type t in
    let b_src, body_src, ref_src =
      mk_named_binding "src" src_buf.typ (EBufSub (src_buf, src_ofs))
    in
    let b_dst, body_dst, ref_dst =
      mk_named_binding "dst" dst_buf.typ (EBufSub (dst_buf, dst_ofs))
    in
    let b_len, body_len, ref_len =
      mk_named_binding "len" uint32 len.node
    in
    let b_len = mark_mut b_len in
    ELet (b_src, body_src, close_binder b_src (with_unit (
    ELet (b_dst, body_dst, close_binder b_dst (with_unit (
    ELet (b_len, body_len, close_binder b_len (with_unit (
      EWhile (
        mk_gt_zero ref_len, with_unit (
        ESequence [ with_unit (
          EBufWrite (
            ref_dst,
            mk_minus_one ref_len,
            with_t (EBufRead (ref_src, mk_minus_one ref_len)))); with_unit (
          EAssign (ref_len, mk_minus_one ref_len))])))))))))))

end

let simplify (files: file list): file list =
  let files = visit_files () remove_buffer_ops files in
  files

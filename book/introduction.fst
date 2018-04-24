module Introduction

/// Introduction
/// ============
///
/// This manual documents Low*, a subset of F* that enjoys compilation to C,
/// using its companion compiler KreMLin. As such, Kre\ **ML**\ in offers an
/// alternative to OCa\ **ML** for extracting and running F* programs (hence the
/// name).
///
/// Low* is not only a language subset, but also a set of F* libraries that
/// model a *curated* set of C features: the C memory model, stack- and
/// heap-allocated arrays, machine integers, C string literals, and a few
/// system-level functions from the C standard library.
///
/// Writing in Low*, the programmer enjoys the full power of F* for proofs and
/// specifications; these are erased as part of the compilation process, meaning
/// that *the code is low-level, but the verification is not*.
///
/// This manual offers a tour of Low* and its companion libraries; presents the
/// tool KreMLin and the various ways it can be used to generate C programs or
/// libraries; covers a few advanced examples.
///
/// Low* has been successfully used to write `HACL*
/// <https://github.com/mitls/hacl-star>`_, a library of verified cryptographic
/// primitives used in Firefox, the Linux Kernel and other projects.
///
/// This tutorial assumes the reader is familiar with F*; if in doubt, head over
/// to its `tutorial <https://fstar-lang.org/tutorial>`_.
///
/// The essence of Low*
/// -------------------
///
/// We take a seminal example, the ``memcpy`` function, which takes a set of
/// elements and copies them from ``src`` to ``dst``. We fully specify it, and
/// compile it to C via KreMLin.

open FStar.HyperStack.ST

module B = FStar.Buffer
module U32 = FStar.UInt32
module S = FStar.Seq
module ST = FStar.HyperStack.ST

let slice_plus_one #a (s1 s2: S.seq a) (i: nat): Lemma
  (requires (
    i < S.length s1 /\
    i < S.length s2 /\
    S.equal (S.slice s1 0 i) (S.slice s2 0 i) /\
    S.index s1 i == S.index s2 i))
  (ensures (
    S.equal (S.slice s1 0 (i + 1)) (S.slice s2 0 (i + 1))))
  [ SMTPat (S.slice s1 0 (i + 1)); SMTPat (S.slice s2 0 (i + 1)) ]
=
  let x = S.index s1 i in
  let s1' = S.append (S.slice s1 0 i) (S.cons x S.createEmpty) in
  let s2' = S.append (S.slice s2 0 i) (S.cons x S.createEmpty) in
  assert (S.equal s1' (S.slice s1 0 (i + 1)));
  assert (S.equal s2' (S.slice s2 0 (i + 1)))

#set-options "--max_fuel 0 --max_ifuel 0"
val memcpy: #a:eqtype -> src:B.buffer a -> dst:B.buffer a -> len:U32.t -> Stack unit
  (requires (fun h0 ->
    B.live h0 src /\ B.live h0 dst /\
    B.length src = U32.v len /\
    B.length dst = U32.v len /\
    B.disjoint src dst))
  (ensures (fun h0 () h1 ->
    B.live h1 src /\
    B.live h1 dst /\
    B.modifies_1 dst h0 h1 /\
    S.equal (B.as_seq h1 dst) (B.as_seq h0 src)))
let memcpy #a src dst len =
  let h0 = ST.get () in
  let inv h (i: nat) =
    B.live h src /\ B.live h dst /\
    B.modifies_1 dst h0 h /\
    i <= U32.v len /\
    S.equal (Seq.slice (B.as_seq h src) 0 i) (Seq.slice (B.as_seq h dst) 0 i)
  in
  let body (i: U32.t{ 0 <= U32.v i /\ U32.v i < U32.v len }): Stack unit
    (requires (fun h -> inv h (U32.v i)))
    (ensures (fun h0 () h1 -> inv h0 (U32.v i) /\ inv h1 (U32.v i + 1)))
  =
    let open B in
    dst.(i) <- src.(i)
  in
  C.Loops.for 0ul len inv body

let main (): St C.exit_code =
  push_frame ();
  let src = B.createL [ 1UL; 2UL ] in
  let dst = B.create 0UL 2ul in
  memcpy src dst 2ul;
  pop_frame ();
  C.EXIT_SUCCESS

/// The resulting C code is as follows:
///
/// .. code-block:: c
///
///    void memcpy__uint64_t(uint64_t *src, uint64_t *dst, uint32_t len)
///    {
///      for (uint32_t i = (uint32_t)0U; i < len; i = i + (uint32_t)1U)
///        dst[i] = src[i];
///    }
///
///    exit_code main()
///    {
///      uint64_t src[2U] = { (uint64_t)1U, (uint64_t)2U };
///      uint64_t dst[2U] = { 0U };
///      memcpy__uint64_t(src, dst, (uint32_t)2U);
///      return EXIT_SUCCESS;
///    }
///
/// This example illustrates many of the central ideas in Low*.
///
/// - **A shallow embedding of C**. The programmer writes F* syntax, bearing in
///   mind that it ought to compile to C, i.e. be in the Low* subset. We offer
///   dedicated primitives, such as the ``C.Loops.for`` function, enabling
///   fine-grained control over the generated C.
///
/// - **A model of C**. The example above relies on a modeling in F* of several
///   C features, such as bounded machine integers, stack-allocated arrays, and
///   the separation between the stack and the heap. Dedicated combinators such
///   as ``push_frame`` and ``pop_frame`` allow reflecting the structure of the call
///   stack using F*'s built-in effect system.
///
/// - **High-level verification of low-level code**. The example contains a vast
///   amount of specification, ranging from temporal safety (liveness) to
///   spatial safety (disjointness, indices within bounds). Imperative data
///   structures, such as buffers or machine integers, are reflected at the
///   proof level with sequences and natural numbers respectively. This allows
///   for a powerful specification style, which ultimately states that after
///   calling ``memcpy``, the ``src`` and ``dst`` buffers are the same up to ``len``.
///   All of this specification is erased, leaving only a succinct, low-level
///   ``for``-loop.
///
/// - **Tooling support for programmer productivity**. The example relies on
///   KreMLin to automatically generate monomorphic instance of the polymorphic
///   ``memcpy`` function above. This is representative of a more general take:
///   whenever there is a predictable compilation scheme for a high-level
///   feature, KreMLin will provide support to enhance the programming
///   experience. In Low*, one enjoys data types, pattern-matching, tuples,
///   which are respectively compiled as C tagged unions, cascading
///   ``if``\ s, or structures passed by value.


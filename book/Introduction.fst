(* {{{ This fslit's file prelude. TODO: find a way to hide this. *)
module Introduction

// Generate a dependency on LowStar.fst which does not have a main but which
// we still want to verify
let _ = LowStar.test_get
(* }}} *)

/// .. fixme-authors::
///     JP Jonathan Protzenko
///
/// Introduction
/// ============
///
/// This manual documents Low*, a subset of F* that enjoys compilation to C
/// through its companion compiler KreMLin. As such, Kre\ **ML**\ in offers an
/// alternative to OCa\ **ML** for extracting and running F* programs (hence the
/// name).
///
/// Low* is not only a language subset, but also a set of F* libraries that
/// model a *curated* set of C features: the C memory model, stack- and
/// heap-allocated arrays, machine integers, C string literals, and a few
/// system-level functions from the C standard library.
///
/// Writing in Low*, the programmer enjoys the full power of F* for proofs and
/// specifications. At compile-time, proofs are erased, leaving only the
/// low-level code to be compiled to C. In short:
///
/// .. centered:: **the code is low-level, but the verification is not**.
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
/// The snippet below implements a classic ``memcpy`` function, copying ``len``
/// elements of type ``a`` from ``src`` into ``dst``.

#set-options "--use_two_phase_tc true"

open FStar.HyperStack.ST

module S = FStar.Seq
module B = LowStar.Buffer
module M = LowStar.Modifies
module U32 = FStar.UInt32
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
  let s1' = S.append (S.slice s1 0 i) (S.cons x S.empty) in
  let s2' = S.append (S.slice s2 0 i) (S.cons x S.empty) in
  assert (S.equal s1' (S.slice s1 0 (i + 1)));
  assert (S.equal s2' (S.slice s2 0 (i + 1)))

open LowStar.BufferOps

#set-options "--max_fuel 0 --max_ifuel 0"
val memcpy: #a:eqtype -> src:B.buffer a -> dst:B.buffer a -> len:U32.t -> Stack unit
  (requires fun h0 ->
    let l_src = M.loc_buffer src in
    let l_dst = M.loc_buffer dst in
    B.live h0 src /\ B.live h0 dst /\
    B.length src = U32.v len /\
    B.length dst = U32.v len /\
    M.loc_disjoint l_src l_dst)
  (ensures fun h0 () h1 ->
    let l_src = M.loc_buffer src in
    let l_dst = M.loc_buffer dst in
    B.live h1 src /\
    B.live h1 dst /\
    M.(modifies l_dst h0 h1) /\
    S.equal (B.as_seq h1 dst) (B.as_seq h0 src))
let memcpy #a src dst len =
  let h0 = ST.get () in
  let inv h (i: nat) =
    B.live h src /\ B.live h dst /\
    M.(modifies (loc_buffer dst) h0 h) /\
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

let main (): Stack C.exit_code
  (requires fun _ -> True)
  (ensures fun h _ h' -> M.modifies M.loc_none h h')
=
  push_frame ();
  let src = B.alloca_of_list [ 1UL; 2UL ] in
  let dst = B.alloca 0UL 2ul in
  memcpy src dst 2ul;
  pop_frame ();
  C.EXIT_SUCCESS

/// This example showcases several features of Low*. We first present the code from
/// a high-level point of view, then show how it compiles to C. We leave a detailed
/// discussion of Low* to the subsequent chapters of this tutorial.
///
/// The code starts by opening several modules that are part of the "Low*
/// standard library".
///
/// - ``Buffer`` is our model of stack- and heap- allocated C arrays
///   (described in :ref:`buffer-library`)
/// - ``Seq`` is the sequence abstraction from the F* standard library, which
///   ``Buffer`` uses to reflect the contents of a given buffer in a given heap
///   at the proof level
/// - ``Modifies`` provides a universal modifies clause over buffers, references
///   and regions (described in :ref:`modifies-library`)
/// - ``UInt32`` is a model of the C11 ``uint32_t`` type, reflected at the proof
///   level using natural numbers (described in :ref:`machine-integers`)
/// - ``HyperStack`` is our model of the C memory layout (described in
///   :ref:`memory-model`)
/// - ``C`` and ``C.Loops`` expose some C concepts to F* (described in
///   :ref:`c-library`)
///
/// The first definition is a lemma over sequences: if two sequences are equal over
/// the slice ``[0; i)`` and their ``i``\ -th element is equal, then they are equal
/// over the slice ``[0; i + 1)``. This lemma is required to prove the functional
/// correctness of ``memcpy``. Lemmas are erased and do not appear in the generated
/// code, so it is safe to mix lemmas with Low* code.
///
/// Next, then ``memcpy`` function is defined and annotated with pre- and
/// post-conditions, using liveness and disjointness predicates. The post-condition
/// states that after calling ``memcpy src dst len``, the destination and the source
/// have the same contents up to index ``len``.
///
/// The implementation of ``memcpy`` uses a C-style ``for`` loop with a loop
/// invariant and a loop body. Alternatively, one could write a recursive function,
/// relying on the C compiler to hopefully perform tail-call optimization.
///
/// Finally, the ``main`` function uses ``push_frame`` and ``pop_frame``, two
/// combinators from the memory model that indicate that this code conceptually
/// executes in a new stack frame. In this new stack frame, two test arrays are
/// allocated on the stack. These are arrays of 64-bit unsigned integers, as denoted
/// by the ``UL`` Low* suffix for machine integers. The ``memcpy`` function is
/// called over these two arrays. From a verification perspective, since the stack
/// frame is freed after calling ``main``, we can successfully state that ``main``
/// modifies no buffer.
///
/// Leaving an in-depth explanation of these concepts to later sections, it
/// suffices to say, for now, that one can invoke the KreMLin compiler to turn
/// this code into C:
///
/// .. code-block:: bash
///
///    $ krml -no-prefix Introduction introduction.fst
///
/// .. warning::
///
///    This tutorial is written using `fslit
///    <https://github.com/FStarLang/fstar-mode.el/tree/master/etc/fslit>`_,
///    meaning that this document is actually an F* source file converted to HTML.
///    The present file is ``Introduction.fst`` and can be found in the ``book``
///    directory of KreMLin. So, you can actually run the command above if you want
///    to try things out for yourself!
///
/// This generates several C files in the current directory. The resulting
/// ``Introduction.c`` is as follows.
///
/// .. code-block:: c
///
///    /* This file was generated by KreMLin <https://github.com/FStarLang/kremlin>
///     * KreMLin invocation: krml -no-prefix Introduction introduction.fst
///     * F* version: 451c4a69
///     * KreMLin version: 3d1941d0
///     */
///
///    #include "Introduction.h"
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
/// This informal presentation highlights several key design points of Low*.
///
/// - **A shallow embedding of C**. The programmer writes F* syntax, bearing in
///   mind that it ought to compile to C, i.e. be in the Low* subset. We offer
///   dedicated primitives, such as the ``C.Loops.for`` function, enabling
///   fine-grained control over the generated C.
///
/// - **A model of C**. The example above relies on modeling several C features in
///   F*, such as bounded machine integers, stack-allocated arrays, and the
///   separation between the stack and the heap. Dedicated combinators such as
///   ``push_frame`` and ``pop_frame`` allow reflecting the structure of the call
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
///
/// Tooling and setup
/// -----------------
///
/// We now show how to get started with the tools and obtain a working F*/KreMLin
/// pair.
///
/// KreMLin is intimately tied with F*:
///
/// - the ``master`` branch of KreMLin works with the ``stable`` branch of F*
/// - the ``fstar-master`` branch of KreMLin works with the ``master`` branch of F*.
///
/// Due to the fast-paced nature of F* development, this tutorial is kept
/// up-to-date with the *latter* set of revisions, meaning that this tutorial
/// expects the user to have:
///
/// - an up-to-date version of F* ``master`` `built from source
///   <https://github.com/FStarLang/FStar/blob/master/INSTALL.md>`__
/// - an up-to-date version of KreMLin ``fstar-master``, `built from source
///   <https://github.com/FStarLang/kremlin/tree/fstar-master/#trying-out-kremlin>`__
/// - a C compiler in the path, preferably a recent version of GCC.
///
/// .. note::
///
///    On Windows, we expect the user to use the same setup as F*, i.e. a Cygwin
///    environment with a `Windows OCaml
///    <https://github.com/fdopen/opam-repository-mingw/>`_, along with the MinGW
///    64-bit compilers installed *as cygwin packages*, i.e. the
///    ``x86_64-w64-mingw32-gcc`` executable, along with the corresponding linker,
///    archiver, etc.
///
/// Usage of the KreMLin tool
/// -------------------------
///
/// The KreMLin compiler comes as a command-line tool ``krml``. As a reminder, ``krml
/// -help`` provides the list of options and warnings along with proper
/// documentation.
///
/// The process of extracting from F* to C involves:
///
/// 1. calling ``fstar.exe`` to generate a set of ``.krml`` files
/// 2. calling ``krml`` on these files to generate a set of C files
/// 3. calling the C compiler to generate an executable.
///
/// KreMLin can automate the first and last steps, and act as a driver for both F*
/// and the C compiler, allowing for a quick edit-compile-cycle. For this present
/// file, one may use:
///
/// .. code-block:: bash
///
///    $ krml introduction.fst -no-prefix Introduction -o test.exe && ./test.exe
///
/// The present tutorial will use this mode exclusively, as it
/// is much easier to use and allows trying out KreMLin without writing a
/// substantial amount of ``Makefile``\ s. Furthermore, one can pass ``.c``, ``.h``,
/// ``.o``, and ``.S`` files to KreMLin, to be included at the right step of the
/// build, along with C linker and compiler options via KreMLin's ``-ccopt`` and
/// ``-ldopt`` options.
///
/// .. fixme:: JP
///
///    Add a forward pointer to section 8.
///
/// However, using KreMLin as a driver is inefficient for two reasons:
///
/// - step 1 uses "legacy" extraction in F*: files are processed sequentially,
///   without caching, and verification is by default not performed (use ``-verify``)
/// - step 3 is not parallel
///
/// Section ?? provides a complete sample Makefile that performs parallel
/// verification and extraction, along with parallel compilation of the resulting C
/// code, using F*'s automated dependency analysis and ``gcc -MM`` for correct,
/// incremental builds.

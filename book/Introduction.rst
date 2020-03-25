Introduction
============

This manual documents Low*, a subset of F* that enjoys compilation to C
through its companion compiler KreMLin. As such, Kre\ **ML**\ in offers an
alternative to OCa\ **ML** for extracting and running F* programs (hence the
name -- also a pun on K&R C).

Low* is not only a language subset, but also a set of F* libraries that
model a *curated* set of C features: the C memory model, stack- and
heap-allocated arrays, machine integers, C string literals, and a few
system-level functions from the C standard library.

Writing in Low*, the programmer enjoys the full power of F* for proofs and
specifications. At compile-time, proofs are erased, leaving only the
low-level code to be compiled to C. In short:

.. centered:: **the code is low-level, but the verification is not**.

This manual offers a tour of Low* and its companion libraries; presents the
KreMLin tool and the various ways it can be used to generate C programs or
libraries; covers a few advanced examples.

Low* has been successfully used to write numerous projects, including:

- `HACL* <https://github.com/mitls/hacl-star>`_, a library of verified
  cryptographic primitives used in Firefox, the Linux Kernel and other projects;
- `EverCrypt <https://hacl-star.github.io/HaclValeEverCrypt.html>`_, a
  multiplexing, agile, abstract cryptographic provider that combines C and ASM
  implementations of state-of-the art cryptographic algorithms;
- `EverQuic <https://github.com/project-everest/everquic-crypto/>`_, an
  implementation of the QUIC packet encryption and decryption,
- `EverParse <https://github.com/project-everest/everparse>`_, a library of
  low-level, zero-copy validators and serializers for parsing binary message
  formats.

This tutorial assumes the reader is familiar with F*; when in doubt, head over
to its `tutorial <https://fstar-lang.org/tutorial>`_. For a research-oriented
perspective on Low*, see the initial ICFP'17 paper and subsequent application
papers on the `publications page
<https://jonathan.protzenko.fr/publications.html>`_.

The essence of Low*
-------------------

Consider the following very simple program:

.. literalinclude:: notfslit/Intro.fst
    :language: fstar

Leaving an in-depth explanation of the code to subsequent sections, suffices to
say, for now, that this code demonstrates:

- authoring a ``main`` function that operates within the special C-like memory
  model, called ``HyperStack.St``, which accounts for stack-based and heap-based
  memory management;
- executing a piece of code within a fresh stack frame (``push_`` and
  ``pop_frame``), reflecting the structure of the call stack using F*'s built-in
  effect system
- dealing with C-like machine integers (``UInt32.t`` and the ``0ul`` literal
  syntax for 32-bit unsigned integers), which are accurately modeled in F* to
  account for the underlying C behavior (e.g. no signed overflow)
- using the ``Buffer`` library which models C arrays, offering stack
  (``alloca``) and heap-based allocations; the library enforces temporal and
  spatial safety, relying on an accurate model of the C standard (e.g. no
  pointer addition unless the base pointer is live);
- generating comments into the resulting C source code (``C.comment``)
- using the ``LowStar.Printf`` library to meta-program a series of stateful
  calls using a printf-like combinator, `evaluated within F*`.

Once compiled by the KreMLin compiler, we obtain the following C code:

.. literalinclude:: ../test/.output/Intro.out/Intro.c
    :language: c
    :start-after: SNIPPET_START: main
    :end-before: SNIPPET_END: main

Once compiled by a C compiler, the output is as follows:

.. code-block:: bash

  Hello from from Low*!
  buffer contents: ff 0 0 0 0 0 0 0

Structure of this manual
------------------------

The goal of this manual is to provide both:

- a user's guide to getting started with Low* and the toolchain, setting up a
  project, its build, the interactive mode, and providing pointers for idiomatic
  examples of how to author code in Low*
- an advanced guide, on how to achieve separate builds, the integration of
  hand-written and auto-generated code, generating static headers, dangers of
  doing so, how to achieve abstraction and modularity in Low*v2, etc.
- a reference manual for the krml tool, including code-generation options and
  tweaks
- a library reference, for all the modules in the ``LowStar`` namespace
- a repository of tips-and-tricks for larger projects, including how to author
  robust proofs, selectively overriding ifuel settings using
  ``allow_inversion``, dangerous patterns to be aware of, etc.

..
  Leaving an in-depth explanation of these concepts to later sections, it
  suffices to say, for now, that one can invoke the KreMLin compiler to turn
  this code into C:

  .. code-block:: bash

     $ krml -no-prefix Introduction introduction.fst

  .. warning::

     This tutorial is written using `fslit
     <https://github.com/FStarLang/fstar-mode.el/tree/master/etc/fslit>`_,
     meaning that this document is actually an F* source file converted to HTML.
     The present file is ``Introduction.fst`` and can be found in the ``book``
     directory of KreMLin. So, you can actually run the command above if you want
     to try things out for yourself!

  This generates several C files in the current directory. The resulting
  ``Introduction.c`` is as follows.

  .. code-block:: c

     /* This file was generated by KreMLin <https://github.com/FStarLang/kremlin>
      * KreMLin invocation: krml -no-prefix Introduction introduction.fst
      * F* version: 451c4a69
      * KreMLin version: 3d1941d0
      */

     #include "Introduction.h"

     void memcpy__uint64_t(uint64_t *src, uint64_t *dst, uint32_t len)
     {
       for (uint32_t i = (uint32_t)0U; i < len; i = i + (uint32_t)1U)
         dst[i] = src[i];
     }

     exit_code main()
     {
       uint64_t src[2U] = { (uint64_t)1U, (uint64_t)2U };
       uint64_t dst[2U] = { 0U };
       memcpy__uint64_t(src, dst, (uint32_t)2U);
       return EXIT_SUCCESS;
     }

  This informal presentation highlights several key design points of Low*.

  - **A shallow embedding of C**. The programmer writes F* syntax, bearing in
    mind that it ought to compile to C, i.e. be in the Low* subset. We offer
    dedicated primitives, such as the ``C.Loops.for`` function, enabling
    fine-grained control over the generated C.

  - **A model of C**. The example above relies on modeling several C features in
    F*, such as bounded machine integers, stack-allocated arrays, and the
    separation between the stack and the heap. Dedicated combinators such as
    ``push_frame`` and ``pop_frame`` allow reflecting the structure of the call
    stack using F*'s built-in effect system.

  - **High-level verification of low-level code**. The example contains a vast
    amount of specification, ranging from temporal safety (liveness) to
    spatial safety (disjointness, indices within bounds). Imperative data
    structures, such as buffers or machine integers, are reflected at the
    proof level with sequences and natural numbers respectively. This allows
    for a powerful specification style, which ultimately states that after
    calling ``memcpy``, the ``src`` and ``dst`` buffers are the same up to ``len``.
    All of this specification is erased, leaving only a succinct, low-level
    ``for``-loop.

  - **Tooling support for programmer productivity**. The example relies on
    KreMLin to automatically generate monomorphic instance of the polymorphic
    ``memcpy`` function above. This is representative of a more general take:
    whenever there is a predictable compilation scheme for a high-level
    feature, KreMLin will provide support to enhance the programming
    experience. In Low*, one enjoys data types, pattern-matching, tuples,
    which are respectively compiled as C tagged unions, cascading
    ``if``\ s, or structures passed by value.

  Tooling and setup
  -----------------

  We now show how to get started with the tools and obtain a working F*/KreMLin
  pair.

  KreMLin is intimately tied with F*:

  - stable branches of F* are matched by corresponding branches of KreMLin
    (e.g. ``v0.9.6+``)
  - the ``master`` branch of KreMLin works with the ``master`` branch of F*

  Due to the fast-paced nature of F* development, this tutorial is kept
  up-to-date with the *latter* set of revisions, meaning that this tutorial
  expects the user to have:

  - an up-to-date version of F* ``master`` `built from source
    <https://github.com/FStarLang/FStar/blob/master/INSTALL.md>`__
  - an up-to-date version of KreMLin ``master``, `built from source
    <https://github.com/FStarLang/kremlin/tree/fstar-master/#trying-out-kremlin>`__
  - a C compiler in the path, preferably a recent version of GCC.

  .. note::

     On Windows, we expect the user to use the same setup as F*, i.e. a Cygwin
     environment with a `Windows OCaml
     <https://github.com/fdopen/opam-repository-mingw/>`_, along with the MinGW
     64-bit compilers installed *as cygwin packages*, i.e. the
     ``x86_64-w64-mingw32-gcc`` executable, along with the corresponding linker,
     archiver, etc.

  Usage of the KreMLin tool
  -------------------------

  The KreMLin compiler comes as a command-line tool ``krml``. As a reminder, ``krml
  -help`` provides the list of options and warnings along with proper
  documentation.

  The process of extracting from F* to C involves:

  1. calling ``fstar.exe`` to generate a set of ``.krml`` files
  2. calling ``krml`` on these files to generate a set of C files
  3. calling the C compiler to generate an executable.

  KreMLin can automate the first and last steps, and act as a driver for both F*
  and the C compiler, allowing for a quick edit-compile-cycle. For this present
  file, one may use:

  .. code-block:: bash

     $ krml introduction.fst -no-prefix Introduction -o test.exe && ./test.exe

  The present tutorial will use this mode exclusively, as it
  is much easier to use and allows trying out KreMLin without writing a
  substantial amount of ``Makefile``\ s. Furthermore, one can pass ``.c``, ``.h``,
  ``.o``, and ``.S`` files to KreMLin, to be included at the right step of the
  build, along with C linker and compiler options via KreMLin's ``-ccopt`` and
  ``-ldopt`` options.

  .. fixme:: JP

     Add a forward pointer to section 8.

  However, using KreMLin as a driver is inefficient for two reasons:

  - step 1 uses "legacy" extraction in F*: files are processed sequentially,
    without caching, and verification is by default not performed (the
    ``-verify`` will generate F* errors))
  - step 3 is not parallel

  Section ?? provides a complete sample Makefile that performs parallel
  verification and extraction, along with parallel compilation of the resulting C
  code, using F*'s automated dependency analysis and ``gcc -MM`` for correct,
  incremental builds.

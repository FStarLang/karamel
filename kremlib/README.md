## Implementation of run-time support libraries for KreMLin

This directory contains F\* source files that model various C concepts and
libraries. These are collectively known as the "kremlib".

This directory additionally provides trusted, hand-written implementations:
- of the F\* models from kremlib (in `c/`)
- of selected modules from F\*'s own standard library (also in `c/`, prefixed
  with `fstar_`).

Once built, this directory produces:
- a set of C files ready to be integrated by a consumer into their own source
  tree (in `dist/generic`)
- a pre-built version of libkremlib (as `dist/generic/libkremlib.a`).

This directory also contains partial ML and JavaScript implementations of
kremlib.

### Building kremlib

This Makefile extracts and packages several variants of kremlib, to be found in
the `dist/` subdirectory. The default build is `dist/generic`, and the resulting
object file is `dist/generic/libkremlib.a`.

A client wishing to integrate kremlib in their project should:
- grab `dist/generic`
- leave these files in their own directory
- rely on `Makefile.basic`, a sound, parallel Makefile, to compile and generate
  `libkremlib.a`, then
- pass `libkremlib.a` at the final linking stage.

Clients who have more complex use-cases (shared library, MSVC, 32-bit, ancient
toolchains) should read the remainder of this document.

### What is in kremlib (default build)

The `kremlib/dist/generic` directory contains *numerous* header files for the
F\* standard library modules. These header files are crucial, as they
embody the expected function signatures that kremlib must provide when
implementing some F\* standard library module. They are automatically
re-generated from the source F\* files.

The `kremlib/c` directory contains corresponding *unverified* implementations,
which are hand-written. Each C file, e.g. `kremlib/c/fstar_date.c`, includes
its generated header, e.g. `kremlib/dist/generic/FStar_Date.h`, thus ensuring
that the implementation provides the correct C function prototype.

## Main build variants for kremlib

There are several build configurations supported for kremlib. Remember that
the generated code can be easily customized by passing more KreMLin options
(e.g. `-fparentheses`).

### The default build (`dist/generic`)

The default build:
- assumes a 64-bit target and either GCC or clang
- includes every implementation found in `kremlib/c`
- includes `FStar.UInt128` with external linkage.

### The minimalistic builds (`dist/minimal`)

The generic build configuration above includes as much as possible in terms of
implementations. However, one oftentimes wishes to restrict the amount of files
present in kremlib. To that end, the `dist/minimal` directory contains a
barebones kremlib, made up of *only* the machine integers.

### A verified, universal FStar.UInt128 implementation (`dist/uint128`)

For clients that wish to use a verified uint128 implementation from C, the
`dist/uint128` directory contains a self-contained, standalone implementation of
`FStar.UInt128`. It must be compiled with `-DKRML_VERIFIED_UINT128`.

In the event that the target platform does not support `unsigned __int128`, this
implementation can be used in lieu of `dist/{generic,minimal}/FStar_UInt128.h`
and `dist/{generic,minimal}/fstar_uint128.h`.

### An unverified, MSVC-specific FStar.UInt128 implementation

The implementation of `FStar.UInt128` in the default build relies on `unsigned
__int128`, a GCC/Clang-specific extension. In the event that one should wish to
build with MSVC, it suffices to use `dist/generic/fstar_uint128_msvc.c` instead
of `dist/generic/fstar_uint128.c`.  The `fstar_uint128_msvc.c` file relies on
compiler intrinsics, unless `KRML_VERIFIED_UINT128` is defined, in which case it
uses the slow, verified implementation (see immediately above).

No Makefile is provided for this build configuration, but the user might wish to
take inspiration from https://github.com/project-everest/mitls-fstar/blob/master/src/windows/kremlib/makefile.vs

One can also use `fstar_uint128_msvc.c` in the `minimal` build configuration.

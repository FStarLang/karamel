## Implementation of run-time support libraries for KaRaMeL

This directory contains F\* source files that model various C concepts and
libraries. These are collectively known as the "krmllib".

This directory additionally provides trusted, hand-written implementations:
- of the F\* models from krmllib (in `c/`)
- of selected modules from F\*'s own standard library (also in `c/`, prefixed
  with `fstar_`).

Once built, this directory produces:
- a set of C files ready to be integrated by a consumer into their own source
  tree (in `dist/generic`)
- a pre-built version of libkrmllib (as `dist/generic/libkrmllib.a`).

This directory also contains partial ML and JavaScript implementations of
krmllib.

### Building krmllib

This Makefile extracts and packages several variants of krmllib, to be found in
the `dist/` subdirectory. The default build is `dist/generic`, and the resulting
object file is `dist/generic/libkrmllib.a`.

A client wishing to integrate krmllib in their project should:
- grab `dist/generic`
- leave these files in their own directory
- rely on `Makefile.basic`, a sound, parallel Makefile, to compile and generate
  `libkrmllib.a`, then
- pass `libkrmllib.a` at the final linking stage.

Clients who have more complex use-cases (shared library, MSVC, 32-bit, ancient
toolchains) should read the remainder of this document.

### What is in krmllib (default build)

The `krmllib/dist/generic` directory contains *numerous* header files for the
F\* standard library modules. These header files are crucial, as they
embody the expected function signatures that krmllib must provide when
implementing some F\* standard library module. They are automatically
re-generated from the source F\* files.

The `krmllib/c` directory contains corresponding *unverified* implementations,
which are hand-written. Each C file, e.g. `krmllib/c/fstar_date.c`, includes
its generated header, e.g. `krmllib/dist/generic/FStar_Date.h`, thus ensuring
that the implementation provides the correct C function prototype.

## Main build variants for krmllib

There are several build configurations supported for krmllib. Remember that
the generated code can be easily customized by passing more KaRaMeL options
(e.g. `-fparentheses`).

### The default build (`dist/generic`)

The default build:
- assumes a 64-bit target and either GCC or clang
- includes every implementation found in `krmllib/c`
- includes `FStar.UInt128` with external linkage.

### The minimalistic builds (`dist/minimal`)

The generic build configuration above includes as much as possible in terms of
implementations. However, one oftentimes wishes to restrict the amount of files
present in krmllib. To that end, the `dist/minimal` directory contains a
barebones krmllib, made up of *only* the machine integers.

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
take inspiration from https://github.com/project-everest/mitls-fstar/blob/master/src/windows/krmllib/makefile.vs

One can also use `fstar_uint128_msvc.c` in the `minimal` build configuration.

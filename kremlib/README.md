## Implementation of run-time support libraries for KreMLin

This directory contains F\* source files that model various C concepts and
libraries, along with corresponding C and OCaml implementations. These are
collectively known as the "kremlib".

The C version of kremlib implements not only the modules present in this
directory, but also provides implementations for a subset of the modules in F\*'s
own standard library that make sense in a C context.

### Building kremlib

The top-level Makefile, right after compiling the krml tool, compiles kremlib,
producing a single archive file `out/libkremlib.a`. This file must be
provided when linking KreMLin-generated programs. The KreMLin tool will do this
automatically when acting as a compilation driver.

### What is in kremlib

The `kremlib/extracted` directory contains *numerous* header files for the F\*
standard library modules. These header files are crucial, as they embody the
expected function signatures that kremlib must provide when implementing some F\*
standard library module. They are automatically re-generated from the source F\*
files.

The `kremlib/c` directory contains corresponding *unverified* implementations,
which are hand-written. Each C file, e.g. `kremlib/c/fstar_date.c`, includes
its generated header, e.g. `kremlib/extracted/FStar_Date.h`, thus ensuring
that the implementation provides the correct C function prototype.

## Main build variants for kremlib

There are five main build configurations supported for kremlib. Remember that
the generated code can be easily customized by passing more KreMLin options
(e.g. `-fparentheses`).

### The default build

The default build:
- assumes a 64-bit target and the either GCC or clang
- includes every implementation found in `kremlib/c`
- includes `FStar.UInt128` with external linkage.

This target is built via `kremlib/Makefile`, and the set of sources required to
construct `out/libkremlib.a` can be found in the `SOURCES` variable in
`kremlib/Makefile`. The sources of this build have to be manually collected
across the `c` and `extracted` directories.

### The MSVC build

The implementation of `FStar.UInt128` in the default build relies on `unsigned
__int128`, a GCC/Clang-specific extension. In the event that one should wish to
build with MSVC, it suffices to replace `c/fstar_uint128.c` in the `SOURCES`
above with `c/fstar_uint128_msvc.c`. That latter file relies on compiler
intrinsics, unless `KRML_VERIFIED_UINT128` is defined, in which case it uses the
slow, verified implementation (see immediately below).

No Makefile is provided for this build configuration, but the user might wish to
take inspiration from https://github.com/project-everest/mitls-fstar/blob/master/src/windows/kremlib/makefile.vs

### The slow, universal build

If neither MSVC or 64-bit GCC/Clang are available, a third build option is
available. It consists in replacing `c/fstar_uint128.c` in `SOURCES` with
`extracted/FStar_UInt128.c`, a verified, slow implementation of `uint128` that
does not rely on compiler-specific suppport.

**Warning:** in this build configuration, the KreMLin-extracted source files
MUST BE compiled with `-DKRML_VERIFIED_UINT128`.

No Makefile is provided for this build configuration.

### The minimalistic builds

The three build configurations above include as much as possible in terms of
implementations. However, one oftentimes wishes to restrict the amount of files
present in kremlib. To that end, the `dist/minimal` directory contains a
barebones kremlib, made up of *only* the machine integers. The `fstar_uint128.c`
file in that directory can be customized with any of the three variants above.

### The uint128 build

For clients that wish to use a verified uint128 implementation from C, the
`dist/uint128` directory contains a self-contained, standalone implementation of
`FStar.UInt128`.

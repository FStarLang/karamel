## Implementation of run-time support libraries for KreMLin

This directory contains F* source files that model various C concepts and
libraries, along with corresponding C and OCaml implementations. These are
collectively known as the "kremlib".

The C version of kremlib implements not only the modules present in the present
directory, but also provides implementations for a subset of the modules in F*'s
own standard library that make sense in a C context.

### Building kremlib

The top-level Makefile, right after compiling the krml tool, compiles kremlib,
producing a single archive file `out/libkremlib.a`. This file must be
provided when linking KreMLin-generated programs. The KreMLin tool will do this
automatically when acting as a compilation driver.

### What is in kremlib

The `kremlib/extracted` directory contains *numerous* header files for the F*
standard library modules. These header files are crucial, as they embody the
expected function signatures that kremlib must provide when implementing some F*
standard library module. They are automatically re-generated from the source F*
files.

The `kremlib/c` directory contains corresponding implementations, which are
hand-written. Each C file, e.g. `kremlib/c/fstar_date.c`, includes its generated
header, e.g. `kremlib/extracted/FStar_Date.h`, thus ensuring that the
implementation provides the correct C function prototype.

### Choosing an implementation of FStar.UInt128

The provided Makefile compiles `libkremlib.a` with GCC and relies on
`__unsigned int128` to implement `FStar_UInt128_uint128`, via
`c/fstar_uint128.c`.

When using MSVC, `c/fstar_uint128.c` must be ignored and
`c/fstar_uint128_msvc.c` must be used instead. The following series of commands
create a static library using MSVC (sketch):

```
rm c/fstar_uint128.c
cl /I ../include /I generated /C c/*.c
lib /OUT:libkremlib.obj c/*.obj
```

There is no provided Makefile of Visual Studio project for this scenario.

Finally, if one wishes to use the verified implementation of `FStar.UInt128`,
extracted from F*'s `ulib/FStar.UInt128.fst`, it suffices to use
`extracted/FStar_UInt128.c` and to define the macro `KRML_EXTRACTED_UINT128`.

Sketch:

```
find c -not -iname 'fstar_uint128*' -and -iname '*.c' | \
  xargs gcc -I ../include -I extracted -DKRML_VERIFIED_UINT128 \
    -Wall -Wextra -Wno-parentheses -c extracted/FStar_UInt128.c
ar cr out/libkremlib-verified-uint128.a *.o
```

There is no provided Makefile target for this scenario.

Client code does *not* need to be recompiled to use one uint128 implementation
or the other. The -extract-uint128 option used by kremlib/Makefile is *for
internal use only* and is intentionally left undocumented.

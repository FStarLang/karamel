### November 20th, 2017

- New -minimal option to disable #include "kremlib.h" and -bundle FStar.*
- krembytes.h, a library in support of value bytes, backed by a conservative GC,
  modeled in ulib/FStar.Bytes.fsti -- see the command-line parameters in
  test/Makefile for TestKremBytes.fst

### November 16th, 2017

- New Warning 13: monomorphic instance inserted in a module that's about to be
  dropped, you may get errors later on.
- Support for equality at non-base types; this generates "external" function
  declarations, to be filled out by the user. Example:

  let f (x y: bytes) = 
    if x = y then
      ...

  generates:

  extern bool __eq__FStar_Bytes_bytes(FStar_Bytes_bytes x, FStar_Bytes_bytes y);

  in this case, the function is implemented in krembytes.h, but in the general
  case, the user will want to declare it in a .c file to be passed to KreMLin.

### November 15th, 2017

Big cleanup in the treatment of strings.

- C.string is a low-level string that can be blitted into a buffer, and is
  revelead to be zero-terminated. Support is in `kremlib/C.String.fst`, and
  clients will need `-add-include '"kremstr.h"'`.
- Prims.string is a value type that supports operations such as `(^)` and is
  backed by a GC. Support is in `ulib/FStar.String.fst` and
  `FStar.HyperStack.IO.fst`. Clients will need to pass `kremstr.c` to KreMLin.
- Users will need to replace `C.print_string (C.string_of_literal "foo")` with
  `C.String.print (C.String.of_literal "foo")` -- the useless two definitions in
  `C.fst` that were there very early on for debugging have been deprecated for a
  while and are now gone.

### November 14th, 2017

New features.

- A new `-add-early-include` option that generates `#include <<your-file>>` at
  the very beginning of the file; this is useful to define host-specific macros,
  e.g. `KRML_HOST_MALLOC`, or simply to do `#define KRML_NOUINT128` before
  `kremlib.h` gets included
- a `!*` operator in `C.Nullity.fsti` that guarantees that `!*p` gets
  pretty-printed as `*p` rather than `p[(uint32_t)0U]`
- `C.Failure`, a new module that allows you to write things like:
  `C.Failure.failwith !$"unexpected"`, where `failwith` returns any type you want
  (trick courtesy of Nik)
- `intptr_t` exposed as an abstract type in `C.fst`, and an abstract value of
  that type, called `nullptr` -- to carry around opaque pointer values that will
  be used from C
- `C.String.print` function
- A distinguished `C.Nullity.fsti` module (in `fstar-master`) that allows you to
  talk about null pointers.
  - In particular, one should not call `Buffer.create` with length 0 -- this is
    an original mistake as it results in C undefined behavior; please use
    `C.Nullity.null <your-type>`, the lemmas from this module reveal that a null
    pointer is always live and always has length 0
  - This module gets special support; `C.Nullity.null <your-type>` becomes
    `NULL` and `C.Nullity.is_null e` becomes `e == NULL`


### November 10th, 2017

Deprecation of `-drop`, because monomorphization may insert useful instances at
any point in the program (at their first use-site), and the new reachability
analysis allows one to easily get rid of un-needed code.

New reachability analysis.
- Elimination of unused globals, externals, types and function definitions (i.e.
  all types of KreMLin declarations) based on reachability. Reminder: the
  reachability analysis starts from:
  - the `main` of your program, if any
  - the public functions
- The interaction with bundling remains the same:
  - `-bundle Foo.*` groups all the matching modules in a single C translation
    unit, marking everything as private (i.e. unreachable), unless for those
    functions that are called from outside the bundle
  - `-bundle Api=Foo.*` groups all the `Foo.*` modules in a single C translation
    unit, and appends `Api` without any visibility modifications, meaning that
    the public functions in `Api` are now the roots of the reachability
    analysis.

Example.
- For krml-test-hacl.exe, we no longer rely on `-drop` at all, but instead on
  these two `-bundle` arguments:
  - `-bundle "Crypto.AEAD.Main=Crypto.*"` ("group all the Crypto.* modules in a
    single C file, then starting from the non-private top-level declarations
    of Crypto.AEAD.Main, perform a reachability analysis, and drop everything
    that's not reachable"), and
  - `-bundle Hacl.Impl.Poly1305_64+Hacl.Impl.Chacha20=Hacl.*,Spec,Spec.*` (same
    thing, with two modules for the roots of the reachability analysis, and
    the spec modules in there too, so that their contents are naturally
    eliminated too)...

New syntax for `-bundle`:
- The `-bundle` option now accepts a `+`-separated list of modules as the
  left-hand-side of the bundle (see above).


### November 6th, 2017

KreMLin is now much smarter about mutual recursion, parameters and type
definitions; we now support parameterized, mutually recursive type definitions,
with the following caveats:
- the type must have a finite size in C (i.e. the C compiler will bail out if it
  doesn't) -- this rules out things like `type t a = T: t a -> t a` -- insert a
  `Buffer.buffer` indirection!
- if `t1` and `t2` are mutually recursive, the order is unspecified, i.e. you may
  get a forward declaration of `t2` (i.e. `typedef struct t2_s t2`; in C), the
  declaration of `t1` (`typedef { ... fields of t1 ... } t1;`), then the declaration
  of `t2` (`typedef struct t2_s { ... actual fields ... } t2;`), or the opposite
- the size of the type graph must be finite, i.e. kremlin will happily loop on
  `type t a = | C: t (a * a) -> t a | D`
- if a polymorphic type definition is missing, but some code still refers to it,
  then kremlin will assign names to the instances, along with forward
  declarations, i.e. if you decided to `-drop Foo`, but still had `type t =
  Foo.u int32` in your code, then you'd get `typedef struct Foo_u_int32_s
  Foo_u_int32;`
  followed by `typedef Foo_u_int32 t;` and then you'd have to provide by hand a
  definition of `Foo_u_int32`

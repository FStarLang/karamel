### Aug 4th, 2020

- New feature: -fextern-c wraps the contents of each header in

```
#if defined(__cplusplus)
extern "C" {
#endif
```

- Better heuristics for picking the name of the monomorphized data types, based
  on the presence of type abbreviations in the original source files.

### Jan 28th, 2020

- New bundle option: rename-prefix (no argument) overrides the original module
  name with the one from the bundle.

### Jan 13th, 2020

- New *experimental* option: `-fmerge`, to merge variables, i.e. reuse existing
  variable slots rather than declare new variables. Improves readability
  especially for meta-programmed code.

### Jan 10th, 2020

- `static` functions that are not defined as `static inline` in the `.h` file
  (i.e. purely in the scope of the `.c` file) will now enjoy short names and
  will drop the long prefix with the original F\* module name -- this may cause
  collisions with functions in scope from included headers. Please shout out if
  this breaks anyone's workflow.

### Jan 9th, 2020

- C++ keywords are now avoided in the code generation for clients who compile
  KreMLin-generated code with C++ compilers.

### Dec 3rd, 2019

- New *experimental* option: `-fnoreturn-else`, to skip `else` statements in
  case the `then` branch can be ended with `return`.

### November 22nd, 2019

- Syntax change for the -static-header option; it now takes a list of patterns
  (like -drop, -library, etc.)

### October 17th, 2019

- New syntax for `-add-include` and `-add-early-include`: `Foo.h:bar` will
  prepend `#include bar` only in the file whose C name is `Foo.h`

### June 27th, 2019

- `[@ deprecated ]` and `[@ (deprecated "message")]` attributes are now
  forwarded to the C compilers, relying on GNU atttribute syntax and MSVC declspec
  syntax.

### May 7th, 2019

- `[@ CMacro ] let x = e` will compile as `#define X (e)` -- the result is
  unspecified if `e` is not a pure C expression; macros follow regular
  visibility rules.

### March 25th, 2019

- A response file mechanism for situations where the combined length of
  command-line arguments exceeds the maximum allowable length (especially on
  Windows). Any argument of the form `@foo.rsp` triggers the reading of
  `foo.rsp` as a response file. A response file is taken to contain one argument
  on each line. Lines may be terminated by LF or CRLF. Line breaks cannot be
  escaped. A response file can be passed in lieu of a .fst file, i.e. you can do
  `krml @foo.rsp` but you cannot do `krml -ccopt @foo.rsp`.

### February 28th, 2019

- `[@ CIfDef ] assume val x` will transform `if x then e1 else e2` using an
  `#ifdef`

### February 26th, 2019

- Data types with a single branch with a single constructor are now completely
  eliminated. This is now a fifth compilation scheme for data types.
- Same thing for records with a single field.

### February 25th, 2019

- Eliminate unit argument within records, too

### January 18th, 2019

- Allow %s in header files (passed to KReMLin via -header), to indicate where to
  insert the KReMLin invocation.

### January 1st, 2019

- Headers now only depend on their direct dependencies. Previously, KreMLin
  would order C files in a valid topological order, then each header would
  include *all the previous headers*. This meant that users could only exclude
  (say, from their build) suffixes of the (unspecified, unstable) topological
  ordering. Now, users are free to exclude any set of modules from their build,
  as long as it creates no unbound symbols.

  This is of particular importance for HACL\* and EverCrypt, as it means that
  consumers can choose to ignore some parts of HACL\*/EverCrypt, should they not
  need it.

### December 28th, 2018

- Overhaul of the various struct transformations. This fixes bugs in the Wasm
  backend, simplifies internal code, and finally gives a working C89 mode that
  properly removes struct literals in favor of gradual initialization, i.e.

  ```
  foobar_t x = { .tag = foo, .val = { .case_Bar = baz }}
  ```

  is now compiled as:

  ```
  foobar_t x;
  x.tag = foo;
  x.val.case_bar = baz;
  ```

  when using `-fno-compound-literals`.

### November 29th, 2018

- The build process of kremlib now produces several flavors in kremlib/dist, all
  of which are standalone; their compilation is under CI. See kremlib/README for
  more details.

### November 27th, 2018

- Allow `-bundle Foo=[rename=Bar]`
- Previously, matching a file twice was a hard error. Now, bundles are
  interpreted left-to-right and the second match is ignored when on the
  right-hand side of "=". This allows: `-bundle Foo,Bar[rename=MyLib] -bundle *[rename=TheRest]`
- Make the topological sort preserve the order of bundles in the
  resulting `#includes`
- KreMLin now generates a basic Makefile that can be used to compile
  your project. kremlib/dist/uint128 and kremlib/dist/minimal are
  examples.

### November 12th, 2018

- When the C file contains no declaration, don't even create it, leave a
  standalone header.

### November 5th, 2018

- Use `uint16_t` when short enums is on, in case the number of cases (pun
  intended) exceeds 255.
- Syntax for renaming bundles; example: `Foo1+...+Foon=Bar1+...+Barn[rename=Foo]`

### September 14, 2018

- Always use the type name in sizeof expressions.
- Support for uninitialized buffers (see test/UBuffer.fst)

### September 11, 2018

- Peephole optimization: `let x = e1 in x` becomes `e1`, useful for compact
  projectors.
- New fatal error, the compilation of a lazy boolean operator gives rise to
  let-bindings, which would change the program semantics. Complete with location
  and offending expression + bindings.

### September 10, 2018

- Don't allocate a struct variable for "full" matches, e.g. `let x, (y, z) = e1,
  (e2, e3)` is now translated as `let x = e1 in let y = e2 in let z = e3`
- Early hoisting of lets outside of scrutinees to increase opportunities for the
  optimization above
- Reparenthesize applications to make sure a higher-order call in Low\* compiles
  properly to C
- Make the treatment of unused arguments uniform, also across function types

### August 28th, 2018

- Support for top-level arrays in the data segment in WASM
- Support for (unchecked) Prims.int in WASM
- Better modularity of the loader in WASM to facilitate integration

### August 27th, 2018

- Remove hand-written, buggy implementation of the `eq_mask` and `gte_mask`
  functions, in favor of verified ones (bug reported by Jason Donenfeld).

### July 22nd, 2018

- Support for a new attribute, `CAbstractStruct`. Such a structure generates a
  forward declaration in the header file, and the concrete struct declaration is
  hidden within the .c file. This forces C clients to always use this struct
  through a pointer, effectively implementing a notion of "C abstract type".

### July 8th, 2018

- New flag: `-library <pattern>`, to indicate that all functions in a given module should be
  turned into `assume val`s. This is useful if: your module is a model and the
  definitions should not leak, or if you are doing separate compilation and the
  pattern captures all the modules in a given library, which have been compiled
  separately and will be provided at link-time.

### June 14th, 2018

- Buffers of size one are now automatically emitted as stack-allocated
  variables.

### June 7th, 2018

- Warning 7 is now emitted only when the bundle does have an Api specified.
  Concretely: `-bundle FStar.*` no longer warns when a function loses its static
  qualifier, as it is understood that these modules should be extracted on an
  "as-needed" basis. However, if a function from `M` loses its static qualifier
  when using `-bundle MyLib=M,N`, then you do get a warning, because it
  indicates that someone (e.g. a test file) is not using `MyLib` through its
  intended entry points.

- Warning 14, for declarations that use non-Low\* concepts but can still be
  compiled using compatibility layers or run-time support (e.g. list, int,
  string, etc.)

### June 6th, 2018

- Allow specifiying the calling convention directly from within F\*. Now, one
  can write:

  ```
  [@ (CCConv "stdcall") ]
  assume val my_asm_routine: B.buffer UInt8.t -> ...
  ```

  which will generate:

  ```
  extern __stdcall void my_asm_routine(uint8_t *x);
  ```

  The `_stdcall` macro is defined in `include/kremlin/internal/callconv.h`. This
  also works for function declarations, not just prototypes.

- Allow writing top-level constant arrays. Examples from the testsuite:

  ```
  let x = B.gcmalloc_of_list HS.root [ 1l; 0l ]

  let main (): St Int32.t =
    B.recall x;
    x.(1ul)
  ```

  generates:

  ```
  int32_t x[2U] = { (int32_t)1, (int32_t)0 };

  int32_t main()
  {
    return x[1U];
  }
  ```

### May 22nd, 2018

- New `-fshort-enums` option that compiles enum constants as macros of type
  uint8_t. This has several advantages:
  - more compact structures
  - no symbol conflicts when doing separate compilation.

### May 17th, 2018

- Release 0.9.6.0
- Support for running as an OPAM package

### May 2nd, 2018

Massive cleanup and refactoring of the .h kremlib files (part 1)

- Directory structure change: include/kremlin/internal contains the
  headers that define macros and functions that KreMLin expects to be
  in scope when generating C code (example: `__cdecl`, `KRML_CHECK_SIZE`,
  etc.), and include/kremlin contains individual .h files for each F\*
  source file
- Naming convention change: include/kremlib.h is a meta-header that
  includes most of what was there before. Individual implementations are
  in include/kremlin and are named after the F\* module that they
  implement (c_string.h, fstar_dyn.h, etc.) or, for non-Low\* features
  like Prims.int and Prims.string, after the feature that they implement
  (prims_int.h, prims_string.h are the only two)
- Entirely removed sketchy macros (#define FStar_HyperStack_mem) in
  favor of built-in definitions that are gracefully reduced to unit types
  if needed via src/Builtin.ml
- Removed, after a long deprecation period, C.exit_success and
  C.exit_failure; use C.EXIT_SUCCESS and C.EXIT_FAILURE instead

### April 30th, 2018

- Output a Makefile.include that lists the generated .c and .h files.

### April 9th, 2018

- Ensure the `noextract` keyword also works for types. This facilitates
  fine-grained control of what goes into the generated C and, by extension, what
  is in your dependency graph or not.

### April 5th, 2018

- WASM backend: inlining criterion based on function size

### March 27th, 2018

- Tame the number of auto-generated `scrut` variables

### March 7th, 2018

- Large series of fixes for the -fnostruct-passing feature.

### Feb 23rd, 2018

- New -ftail-calls option, which compiles tail-calls to while-loops, for
  compilers such as MSVC that hardly ever perform tail-call optimization.

### Feb 8th, 2018

- New -diagnostics option to get a report on things not Low*.

### Feb 5th, 2018

- Optimized compilation scheme for data types. Branches with a single argument
  no longer generate a struct in the union.

  ```
  type t = A | B of t | C of t * t
  ```

  now becomes:

  ```
  typedef enum { A, B, C } tag_t;
  typedef struct {
    tag_t tag;
    union {
      t case_B; // no longer emitting a one-field struct
      struct {
        x0 t;
        x1 t;
      } case C
    } val
  } t;
  ```

- Various WASM backend improvements, with a couple bugs fixed.

### Feb 2nd, 2018

- Optimized compilation scheme for data types. In the case that there is only
  one non-constant constructor, no nesting occurs. `option int` is now:

  ```
  typedef enum { Nil, Cons } tag_option;
  typedef struct {
    tag_option tag;
    int v;
  } option_int;
  ```

- Prettify most of the instances of KRML_CHECK_SIZE and KRML_HOST_MALLOC to use
  a type name instead of a value for the arguments to sizeof.

### January 24th, 2018

- Support for manually-managed memory via `Buffer.rcreate_mm` and
  `Buffer.rfree`, hopefully soon to have better names. These translate to
  regular calls to `malloc` and `free`.

### December 14th, 2017

- Support for separate extraction of various out.krml, to be passed /en masse/
  to KreMLin. Support for this feature is in F\* 69f79f7. Exemplary Makefile is
  at https://github.com/mitls/hacl-star/blob/28d65c2f24e5f6c8a1d032ae978e996475009c7a/secure_api/Makefile.extract#L93

### December 13th, 2017

- Generation of custom equality functions that implement F\*'s notion of
  equality. This means a structural, recursive comparison for data types,
  address comparison for references, and a proper implementation of
  FStar.Buffer.eqb. Equality predicates may be quite large.

### December 11th, 2017

- Remove unused type parameters. This is especially useful for types
  parameterized over an index, or refinement, since it will generate a lot less
  monomorphizations.

### December 7th, 2017

- Complete elimination of uu____ variables whenever possible.

- The first analysis is as follows: if a `uu____` is a read-only expression, and
  if only read-only expressions may be evaluated between its definition and
  use-site, then it is safe to get rid of the `uu____`.... this means no more
  `uu____`'s for things such as:

  ```
    let z = b.(0ul) +^ b.(1ul) in
    let t = b.(let r = b.(1ul) in Int.Cast.int32_to_uint32 r) in
  ```

  which now becomes:

  ```
    int32_t z = b[0U] + b[1U];
    int32_t r = b[1U];
    int32_t t = b[(uint32_t)r];
  ```

- The second analysis is as follows: if `uu___` is an arbitrary expression, and
  if only pure expressions are evaluated between the definition of the `uu____`
  and its use, and if the `uu____` is only used once, then it is safe to get rid
  of the `uu____`.

  This means that things such as:

  ```
    let y = 1l +^ f () in
  ```

  now give the intended output:

  ```
    int32_t y = (int32_t)1 + f();
  ```

- Note that there is no way to remove `uu____`'s for things such as:

  ```
    let x = f () + f ()
  ```

  F* will generate this:

  ```
    let uu___1 = f () in
    let uu___2 = f () in
    let x = uu___1 + uu___2
  ```

  KreMLin will do its best, and will manage to fold in only the first uu___.
  This gives:

  ```
    int32_t uu___1 = f () in
    int32_t x = uu___1 + f();
  ```

### December 4th, 2017

- Pattern-matching on an integer constant now generates a switch.
- Pattern-matches on integer constants and constant-constructor data types now
  always generate a switch, even when a wildcard pattern is present (it becomes
  the default case of the switch).

### November 30th, 2017

- Partial elimination of uu_ intermediary variables.
- Support for while/do, in C.Loops, pretty-printed as a C while loop.
  Restrictions remain on the shape of the condition, and one may get errors of
  the form: "the condition of the while-loop gives rise to let-bindings", along
  with uu__ bindings in the condition. Consider the while combinator
  experimental until better elimination of uu_'s happens.

### November 29th, 2017

- Long-standing feature request finally implemented: the visibility analysis
  (public/private) now also applies to external and type declarations, meaning
  that the types that are local to a given file are now declared in the C file
  instead of the header file.

### November 28th, 2017

- Write out some information in the generated header (command-line, git
  revisions)
- Support for -bundle Foo=*, which, in combination with -minimal, can be used
  for large-scale separate compilation. Example:

  krml Foo.fst -minimal -bundle Foo=* -add-include '"kremlib.h"'

  This will generate a single C file with only the public functions from Foo
  visible.

### November 27th, 2017

- `C.Loops.for64` with a 64-bit loop index

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

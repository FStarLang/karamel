The KreMLin manual
==================

## Interaction with external code

To successfully mix hand-written C code and F* code, the recommended workflow
is:
- model your C functions at the F* level using a `Stubs.fst` file (not an
  `.fsti`) and run `krml -skip-compilation Stubs.fst` to check that the
  generated .h file matches what you're about to provide;
- write other `.fst` files against `Stubs.fst`; extract with `krml -drop Stubs
  stubs.c` or `krml -drop Stubs -ccopt -lstubs`.

KreMLin still needs to see some declarations for your stubs, so that it can
type-check the rest of your program using these stubs. F*, however, just drops
any `.fsti` file, meaning that you need to use an `.fst` instead for KreMLin to
even be aware of these functions. The `-drop` option of KreMLin makes sure that
no `.h` or `.c` is generated, and you can provide hand-written code instead.

Note: you may need to add `-add-include '"stubs.h"'` too, and write `stubs.h` by
hand.

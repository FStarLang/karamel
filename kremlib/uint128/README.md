Standalone implementation of uint128
====================================

This directory packages a verified, standalone implementation of FStar.UInt128
that does not have any dependencies on other F\* headers. The file only depends
on: `inttypes.h`, `stdbool.h` and `kremlin/internal/types.h`. This is only of
interest for advanced users of KreMLin who manually package and distribute
KreMLin-generated code, and want to minimize the amount of files.

This extracted code is suitable for the following scenarios:

- you need a verified uint128 implementation for your C project, and would
  rather take a single file
- you intend to package minimalistic KreMLin-generated code, have no
  dependencies on any of the other `FStar.*` modules, and are content with using
  only `FStar_UInt128.{c,h}`.

The file can be compiled with `cc -I../../include -DKRML_VERIFIED_UINT128
FStar_UInt128.c`.

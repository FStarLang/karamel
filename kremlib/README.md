## Implementation of run-time support libraries for KreMLin

This directory contains two modules, `C` and `TestLib`.
- `C` exports various functions from the C standard library, reveals the
  existence of a couple types, and provides helper functions for endianness
  conversion.
- `TestLib` contains test-oriented routines, e.g. for comparing buffers

`C.ml` and `TestLib.ml` provide the OCaml implementation, if one wishes to extract
F\* code to OCaml, for reference purposes.

The `.h` and `.c` files provide the corresponding C implementation.

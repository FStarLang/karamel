## Distinguished F* libraries and their realization in C, JS or OCaml

This directory contains the "low-level" libraries that are implemented, modeled
and/or designed within KreMLin. The directory names are relatively
self-explanatory.

### C implementations

Some modules are header-only (e.g. krembytes.h), some modules are
header-and-code (e.g. testlib.h and testlib.c), meaning they require the use of
-drop, and some modules are code-only (e.g. the implementation of FStar.String
in kremstr.c). Unless using -minimal, kremlin will pick the right combination of
files for you.

### Javascript implementations for the WASM backend

These are implement in loader.js in the js directory. This is currently
incomplete, and only contains the bare-bones support needed to run the code/
directory of HACL*.

### OCaml implementation for reference purposes

These are badly out of date and are currently not under any sort of regressions
testing.

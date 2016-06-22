#!/bin/bash

set -e

FSTAR_HOME="$(dirname $(which fstar.exe))/.."
HYPERSTACK_LIB="$FSTAR_HOME/examples/low-level/ulib/hyperstack/"
FSTAR_OPTIONS="--lax --trace_error --universes --codegen Kremlin"
FSTAR="fstar.exe --include $HYPERSTACK_LIB $FSTAR_OPTIONS"
CC="clang -fsanitize=undefined,integer -Wall -Wno-shift-op-parentheses \
  -Wno-unused-variable -Werror"

FILES=Chacha01

for f in $FILES; do
  $FSTAR $f.fst
  ../Kremlin.native -write out.krml
  $CC $f.c main.c -o $f
  ./$f
  echo "$f exited with $?"
done

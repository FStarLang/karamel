#!/bin/bash

set -e

# Path-conversion for Windows
FSTAR_HOME="$(dirname $(which fstar.exe))/.."
if which cygpath >/dev/null 2>&1; then
  FSTAR_HOME=$(cygpath -m $FSTAR_HOME)
fi

# Couldn't get clang to work on Windows...
if which clang >/dev/null 2>&1; then
  HAS_CLANG=true
else
  HAS_CLANG=false
fi

# Detection
OPTS="-Wall -Werror -Wno-parentheses -Wno-unused-variable -std=c11"
CLANG_UB="-fsanitize=undefined,integer"
if $HAS_CLANG && clang $CLANG_UB main.c >/dev/null 2>&1; then
  CLANG="clang $CLANG_UB $OPTS"
else
  CLANG="clang $OPTS"
fi

# On OSX, actual GCC is gcc-5; on other systems, gcc gets some recent gcc.
if which gcc-5 >/dev/null 2>&1; then
  GCC=gcc-5
elif which x86_64-w64-mingw32-gcc >/dev/null 2>&1; then
  GCC=x86_64-w64-mingw32-gcc
else
  GCC=gcc
fi
GCC="$GCC $OPTS"

echo GCC is $GCC
echo HAS_CLANG is $HAS_CLANG
if $HAS_CLANG; then
  echo "CLANG is $CLANG"
fi

HYPERSTACK_LIB="$FSTAR_HOME/examples/low-level/"
FSTAR_OPTIONS="--lax --trace_error --codegen Kremlin"
FSTAR="fstar.exe --include $HYPERSTACK_LIB $FSTAR_OPTIONS"

# Currently sitting in examples/low-level
FILES=Chacha

for f in $FILES; do
  $FSTAR $f.fst
  ../Kremlin.native -write out.krml
  if $HAS_CLANG; then
    $CLANG main-$f.c -o $f
    ./$f
    echo "$f/clang exited with $?"
  fi
  $GCC main-$f.c -o $f
  ./$f
  echo "$f/gcc exited with $?"
done

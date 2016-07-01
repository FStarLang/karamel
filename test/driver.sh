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

# On OSX, to get GCC, one needs to call gcc-5; on other systems, the gcc command
# is wired to a recent GCC.
if which gcc-5 >/dev/null 2>&1; then
  GCC=gcc-5
elif which x86_64-w64-mingw32-gcc >/dev/null 2>&1; then
  GCC=x86_64-w64-mingw32-gcc
else
  GCC=gcc
fi
GCC="$GCC $OPTS"

echo GCC is $GCC
if $HAS_CLANG; then
  echo "CLANG is $CLANG"
else
  echo "CLANG was not detected"
fi

HYPERSTACK_LIB="$FSTAR_HOME/examples/low-level/"
FSTAR_OPTIONS="--lax --trace_error --codegen Kremlin"
FSTAR="fstar.exe --include $HYPERSTACK_LIB $FSTAR_OPTIONS"

function test () {
  local fstar_file=$1
  local c_main=$2
  local krml_options=$3
  local out=${fstar_file%fst}exe
  echo "Extracting [$krml_options] $fstar_file + $c_main => $out"
  $FSTAR $fstar_file
  ../Kremlin.native -write out.krml $krml_options
  if $HAS_CLANG; then
    $CLANG $c_main -o $out
    ./$out
    echo "$out/clang exited with $?"
  fi
  $GCC $c_main -o $out
  ./$out
  echo "$out/gcc exited with $?"
}

# These files currently sitting in examples/low-level
test Poly.Poly1305.fst main-Poly1305.c "-vla"
test Chacha.fst main-Chacha.c

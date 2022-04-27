#!/usr/bin/env bash

set -e
set -x

# FIXME: the `opam depext` command should be unnecessary with opam 2.1
opam depext conf-gmp z3.4.8.5 conf-m4

# Install F*
[[ -n "$FSTAR_HOME" ]]
git clone https://github.com/FStarLang/FStar "$FSTAR_HOME"
opam install --deps-only "$FSTAR_HOME/fstar.opam"
OTHERFLAGS='--admit_smt_queries true' make -j 24 -C "$FSTAR_HOME"
grep -v -i fstar < karamel.opam > karamel-nofstar.opam
opam install --deps-only ./karamel-nofstar.opam

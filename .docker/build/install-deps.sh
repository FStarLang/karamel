#!/usr/bin/env bash

set -e
set -x

build_home="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

# Identify the F* branch
if [[ -z "$FSTAR_BRANCH" ]] ; then
    FSTAR_BRANCH=$(jq -c -r '.BranchName' "$build_home"/config.json)
    if [[ -z "$FSTAR_BRANCH" ]] ; then
        FSTAR_BRANCH=master
    fi
fi

# Install F*
[[ -n "$FSTAR_HOME" ]]
git clone --branch $FSTAR_BRANCH https://github.com/FStarLang/FStar "$FSTAR_HOME"
opam update
opam install --deps-only "$FSTAR_HOME/fstar.opam"
OTHERFLAGS='--admit_smt_queries true' make -j 24 -C "$FSTAR_HOME"

sudo "$FSTAR_HOME/.scripts/get_fstar_z3.sh" "/usr/local/bin"

# Install other deps
"$build_home"/install-other-deps.sh

#!/usr/bin/env bash

set -e
set -x

build_home="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd "$build_home/../.."

grep -v '"fstar"' < karamel.opam > karamel-nofstar.opam
opam update
opam install --deps-only ./karamel-nofstar.opam

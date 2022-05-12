#!/usr/bin/env bash

set -e
set -x

grep -v -i fstar < karamel.opam > karamel-nofstar.opam
opam install --deps-only ./karamel-nofstar.opam

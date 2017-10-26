#!/bin/bash

set -e

if [[ "$TRAVIS_OS_NAME" == "linux" ]]; then
  sudo apt-get install --yes libssl-dev opam libgmp-dev libsqlite3-dev g++-5 gcc-5 libc6-dev;
  sudo update-alternatives --install /usr/bin/gcc gcc /usr/bin/gcc-5 200;
  sudo update-alternatives --install /usr/bin/g++ g++ /usr/bin/g++-5 200;
fi

export OPAMYES=true
opam init
eval $(opam config env)
opam install batteries sqlite3 fileutils stdint zarith yojson pprint \
  ppx_deriving_yojson menhir ulex process fix wasm

if [[ "$TRAVIS_OS_NAME" == "linux" ]]; then
  export Z3=z3-4.4.1-x64-ubuntu-14.04;
  wget https://github.com/Z3Prover/z3/releases/download/z3-4.4.1/$Z3.zip;
  unzip $Z3.zip;
  mkdir d8
  wget https://www.dropbox.com/s/35fo94wzrbex9ij/d8?dl=0 -O d8/d8
  chmod a+x d8/d8
fi

git clone --branch master --single-branch --depth 1 https://github.com/FStarLang/FStar.git fstar
git clone --branch master --single-branch --depth 1 https://github.com/mitls-fstar/hacl-star
make -C fstar/src/ocaml-output

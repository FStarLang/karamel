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

git clone https://github.com/project-everest/everest
./everest/everest opam z3

if [[ "$TRAVIS_OS_NAME" == "linux" ]]; then
  wget https://www.dropbox.com/s/r1uj2cqifhz50ri/d8.tar.bz2?dl=0 -O d8.tar.bz2
  tar xjvf d8.tar.bz2
fi

git clone --branch master --single-branch --depth 1 https://github.com/FStarLang/FStar.git fstar
git clone --branch fstar-master --single-branch --depth 1 https://github.com/mitls/hacl-star
make -C fstar/src/ocaml-output
make -C fstar/ulib/ml

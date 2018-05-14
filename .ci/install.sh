#!/bin/bash

set -e

git config --global user.name "Dzomo, the Everest Yak"
git config --global user.email "everbld@microsoft.com"

git clone https://github.com/fstarlang/fstar-mode.el
git clone https://dzomo:$DZOMO_TOKEN@github.com/fstarlang/fstarlang.github.io

if [[ "$TRAVIS_OS_NAME" == "linux" ]]; then
  sudo apt-get install --yes libssl-dev opam libgmp-dev libsqlite3-dev g++-5 gcc-5 libc6-dev;
  sudo update-alternatives --install /usr/bin/gcc gcc /usr/bin/gcc-5 200;
  sudo update-alternatives --install /usr/bin/g++ g++ /usr/bin/g++-5 200;
fi

sudo easy_install docutils sphinx sphinx-rtd-theme

export OPAMYES=true
export OPAMJOBS=4
opam init --comp=4.05.0
eval $(opam config env)

git clone https://github.com/project-everest/everest
./everest/everest --yes opam z3

if [[ "$TRAVIS_OS_NAME" == "linux" ]]; then
  wget https://www.dropbox.com/s/r1uj2cqifhz50ri/d8.tar.bz2?dl=0 -O d8.tar.bz2
  tar xjvf d8.tar.bz2
fi

git clone --branch master --single-branch --depth 1 https://github.com/FStarLang/FStar.git fstar
git clone --branch cleanup-kremlib-2 --single-branch --depth 1 https://github.com/mitls/hacl-star
make -C fstar/src/ocaml-output
make -C fstar/ulib/ml

#!/bin/bash

set -e

git config --global user.name "Dzomo, the Everest Yak"
git config --global user.email "everbld@microsoft.com"

git clone https://github.com/fstarlang/fstar-mode.el
git clone https://dzomo:$DZOMO_TOKEN@github.com/fstarlang/fstarlang.github.io

sudo apt-get install opam python3
sudo easy_install docutils sphinx==1.7.2 sphinx-rtd-theme

export OPAMYES=true
export OPAMJOBS=4
opam init --comp=4.05.0
eval $(opam config env)

git clone https://github.com/project-everest/everest
./everest/everest --yes opam z3

if [[ "$TRAVIS_OS_NAME" == "linux" ]]; then
  wget https://nodejs.org/dist/v8.11.3/node-v8.11.3-linux-x64.tar.xz
  tar xvf node-v8*.tar.xz
  rm -rf node-v8*.tar.xz
  mv node-v8* node
fi

git clone --branch taramana_buffer_fill --single-branch --depth 1 https://github.com/FStarLang/FStar.git fstar
git clone --branch fstar-master --single-branch --depth 1 https://github.com/mitls/hacl-star
make -C fstar/src/ocaml-output
make -C fstar/ulib/ml -j 4

#!/bin/bash

set -e

eval $(opam config env)
export PATH=/home/travis/build/FStarLang/kremlin/everest/z3/bin:$PATH
export PATH=/home/travis/build/FStarLang/kremlin:$PATH
export PATH=/home/travis/build/FStarLang/kremlin/d8:$PATH
export PATH=/home/travis/build/FStarLang/kremlin/fstar/bin:$PATH
export FSTAR_HOME=/home/travis/build/FStarLang/kremlin/fstar
export HACL_HOME=/home/travis/build/FStarLang/kremlin/hacl-star
export KRML_HOME=/home/travis/build/FStarLang/kremlin
export KREMLIN_HOME=/home/travis/build/FStarLang/kremlin
export OCAMLRUNPARAM=b

echo "\"everest\": -traverse" >> _tags
echo "\"fstar\": -traverse" >> _tags
echo "\"hacl-star\": -traverse" >> _tags
echo "\"d8\": -traverse" >> _tags
echo "\"MLCrypto\": -traverse" >> _tags

echo -e "\e[31m=== Some info about the environment ===\e[0m"
ocamlfind ocamlopt -config
gcc --version
fstar.exe --version
echo | $(which d8)

# Warm up, so that the checked files for these are only generated once, and can
# be reused by krml-test.
make -C fstar/ulib
make && make -C test all wasm external

make -C book html
git clone https://dzomo:$DZOMO_TOKEN@github.com:fstarlang/fstarlang.github.io
cd fstarlang.github.io
cp -R ../book/_build/* lowstar/
git add lowstar/
if [ ! git diff --exit-code > /dev/null ]; then
  git commit -am "[CI] Refresh Low* tutorial"
  git push
else
  echo No git diff for the tutorial, not generating a commit
fi

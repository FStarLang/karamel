#!/bin/bash

set -e

eval $(opam config env)
export PATH=/home/travis/build/FStarLang/kremlin/everest/z3/bin:$PATH
export PATH=/home/travis/build/FStarLang/kremlin:$PATH
export PATH=/home/travis/build/FStarLang/kremlin/fstar/bin:$PATH
export PATH=/home/travis/build/node/bin:$PATH
export FSTAR_HOME=/home/travis/build/FStarLang/kremlin/fstar
export HACL_HOME=/home/travis/build/FStarLang/kremlin/hacl-star
export KRML_HOME=/home/travis/build/FStarLang/kremlin
export KREMLIN_HOME=/home/travis/build/FStarLang/kremlin
export OCAMLRUNPARAM=b

echo "\"everest\": -traverse" >> _tags
echo "\"fstar\": -traverse" >> _tags
echo "\"hacl-star\": -traverse" >> _tags
echo "\"node\": -traverse" >> _tags
echo "\"MLCrypto\": -traverse" >> _tags
echo "\"fstar-mode.el\": -traverse" >> _tags
echo "\"fstarlang.github.io\": -traverse" >> _tags

echo -e "\e[31m=== Some info about the environment ===\e[0m"
ocamlfind ocamlopt -config
gcc --version
fstar.exe --version
node --version

OTHERFLAGS="--admit_smt_queries true" make -C $FSTAR_HOME/ulib -j 4 > ulib-log || exit 255
#make -j 4 && make -C test everything -j 4 || exit 255
make -j 4 && make -C test hacl-wasm -j 4 || exit 255

# Tutorial refresh, only on master and not for pull requests
if [[ $TRAVIS_BRANCH == "master" && $DZOMO_TOKEN != "" ]]; then
  make -C book html
  cd fstarlang.github.io
  git pull
  cp -R ../book/_build/* lowstar/
  rm -rf lowstar/html/static
  mv lowstar/html/_static lowstar/html/static
  find lowstar/html -type f | xargs sed -i 's/_static/static/g'
  git add -A lowstar/html/ lowstar/index.html
  if ! git diff --exit-code HEAD > /dev/null; then
    git commit -m "[CI] Refresh Low* tutorial"
    git push
  else
    echo No git diff for the tutorial, not generating a commit
  fi
fi

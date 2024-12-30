#!/bin/bash

set -eux

# Run from the root of the repo, with a built book, and DZOMO_GITHUB_TOKEN set
# in the environment. This is called by ci.yml on every push to master.

git clone "https://$DZOMO_GITHUB_TOKEN@github.com/fstarlang/fstarlang.github.io"

pushd fstarlang.github.io

cp -R ../book/_build/* lowstar/
rm -rf lowstar/html/static
mv lowstar/html/_static lowstar/html/static
find lowstar/html -type f | xargs sed -i 's/_static/static/g'
git add -A lowstar/html lowstar/index.html

git status

if ! git diff --exit-code HEAD > /dev/null; then
  git commit -m '[CI] Refresh Low* tutorial'
  git push
else
  echo "No git diff for the tutorial"
fi

exit 0

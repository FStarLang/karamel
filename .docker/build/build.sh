#!/usr/bin/env bash

#set -x

target=$1
out_file=$2
threads=$3
branchname=$4

function export_home() {
    local home_path=""
    if command -v cygpath >/dev/null 2>&1; then
        home_path=$(cygpath -m "$2")
    else
        home_path="$2"
    fi

    export $1_HOME=$home_path

    # Update .bashrc file
    local s_token=$1_HOME=
    if grep -q "$s_token" ~/.bashrc; then
        sed -i -E "s@$s_token.*@$s_token$home_path@" ~/.bashrc
    else
        echo "export $1_HOME=$home_path" >> ~/.bashrc
    fi
}

# Note: this performs an _approximate_ refresh of the hints, in the sense that
# since the hint refreshing job takes about 80 minutes, it's very likely someone
# merged to $CI_BRANCH in the meanwhile, which would invalidate some hints. So, we
# reset to origin/$CI_BRANCH, take in our hints, and push. This is short enough that
# the chances of someone merging in-between fetch and push are low.
function refresh_hints() {
    local remote=$1
    local extra="$2"
    local msg="$3"
    local hints_dir="$4"

    # Figure out the branch
    CI_BRANCH=${branchname##refs/heads/}
    echo "Current branch_name=$CI_BRANCH"

    # Add all the hints, even those not under version control
    find $hints_dir -iname '*.hints' -and -not -path '*/.*' -and -not -path '*/dependencies/*' | xargs git add

    # Without the eval, this was doing weird stuff such as,
    # when $2 = "git ls-files src/ocaml-output/ | xargs git add",
    # outputting the list of files to stdout
    eval "$extra"

    git commit --allow-empty -m "[CI] $msg"

    # Memorize that commit
    commit=$(git rev-parse HEAD)

    # Drop any other files that were modified as part of the build (e.g.
    # parse.fsi)
    git reset --hard HEAD

    # Move to whatever is the most recent master (that most likely changed in the
    # meantime)
    git fetch
    git checkout $CI_BRANCH
    git reset --hard origin/$CI_BRANCH

    # Silent, always-successful merge
    export GIT_MERGE_AUTOEDIT=no
    git merge $commit -Xtheirs

    # Push.
    git push $remote $CI_BRANCH
}

function refresh_tutorial_is_enabled () {
    [[ "$OS" != "Windows_NT" ]] &&
    [[ $branchname == "master" ]]
}

function misc () {
  git config --global user.name "Dzomo, the Everest Yak"
  git config --global user.email "everbld@microsoft.com"

  git clone https://github.com/fstarlang/fstar-mode.el

  echo After cloning fstar-mode.el
  
  if refresh_tutorial_is_enabled ; then
      git clone git@github.com:fstarlang/fstarlang.github.io fstarlang-github-io
  fi

  echo Creating _tags
  touch _tags
  echo Populating _tags

  echo "\"everest\": -traverse" >> _tags
  echo "\"fstar\": -traverse" >> _tags
  echo "\"node\": -traverse" >> _tags
  echo "\"MLCrypto\": -traverse" >> _tags
  echo "\"fstar-mode.el\": -traverse" >> _tags
  if refresh_tutorial_is_enabled ; then
      echo "\"fstarlang-github-io\": -traverse" >> _tags
  fi

  export OCAMLRUNPARAM=b

  echo Done with misc
}

function refresh_tutorial() {
  if refresh_tutorial_is_enabled ; then
    make -C book html &&
    pushd fstarlang-github-io && {
        git pull &&
        cp -R ../book/_build/* lowstar/ &&
        rm -rf lowstar/html/static &&
        mv lowstar/html/_static lowstar/html/static &&
        find lowstar/html -type f | xargs sed -i 's/_static/static/g' &&
        git add -A lowstar/html/ lowstar/index.html &&
        if ! git diff --exit-code HEAD > /dev/null; then
            git commit -m "[CI] Refresh Low* tutorial" &&
            git push
        else
            echo No git diff for the tutorial, not generating a commit
        fi
        errcode=$?
    } &&
    popd &&
    return $errcode
  fi
}

function check_version_controlled() {
  make -C kremlib/dist/generic -f Makefile.basic -j
}

function exec_build() {

    # this is a special file that is parsed by Azure Devops
    result_file="../result.txt"

    if misc && check_version_controlled && make -j $threads && \
      make -C test everything -j $threads && \
      make -C book/tutorial && \
      refresh_tutorial
    then
        echo "Build succeeded"
        echo Success >$result_file
    else
        echo "Build failed"
        echo Failure >$result_file
    fi
}

# Some environment variables we want
export OCAMLRUNPARAM=b
export OTHERFLAGS="--print_z3_statistics --use_hints --query_stats"
export MAKEFLAGS="$MAKEFLAGS -Otarget"

export_home FSTAR "$(pwd)/FStar"
export_home KREMLIN "$(pwd)/kremlin"
export_home KRML "$(pwd)/kremlin"

export PATH=$FSTAR_HOME/bin:$PATH
echo $PATH

cd kremlin
rootPath=$(pwd)
exec_build
cd ..

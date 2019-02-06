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

# By default, HACL* master works against F* stable. Can also be overridden.
function fetch_hacl() {
    if [ ! -d hacl-star ]; then
        git clone https://github.com/mitls/hacl-star hacl-star
    fi

    cd hacl-star
    git fetch origin
    local ref=$(jq -c -r '.RepoVersions["hacl_version"]' "$rootPath/.docker/build/config.json" )
    if [[ $ref == "" || $ref == "null" ]]; then
        echo "Unable to find RepoVersions.hacl_version on $rootPath/.docker/build/config.json"
        return -1
    fi

    echo Switching to HACL $ref
    git reset --hard $ref
    git clean -fdx
    cd ..
    export_home HACL "$(pwd)/hacl-star"
    export_home EVERCRYPT "$(pwd)/hacl-star/providers"
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

function exec_build() {

    # this is a special file that is parsed by Azure Devops
    result_file="../result.txt"

    fetch_hacl

    if make -j $threads && \
      make -C test everything -j $threads
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

cd kremlin
rootPath=$(pwd)
exec_build
cd ..

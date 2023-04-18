#!/usr/bin/env bash

set -x

set -e # abort on errors

threads=$1
branchname=$2

build_home="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
. "$build_home"/build_funs.sh

rootPath=$(pwd)
export_home KRML "$rootPath"
result_file="result.txt"
out_file="log.txt"
remove_credentials () {
    if [[ -n "$DZOMO_GITHUB_TOKEN" ]] ; then
        sed "s!$DZOMO_GITHUB_TOKEN!!g"
    else
        cat
    fi
}
{ { { { { { exec_build ; } 3>&1 1>&2 2>&3 ; } | sed -u 's!^![STDERR]!' ; } 3>&1 1>&2 2>&3 ; } | sed -u 's!^![STDOUT]!' ; } 2>&1 ; } | awk '{ print strftime("[%Y-%m-%d %H:%M:%S]"), $0 }' | remove_credentials | tee $out_file

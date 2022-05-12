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
exec_build $target

grep Success < "$result_file"

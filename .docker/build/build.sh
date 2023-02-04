#!/usr/bin/env bash

#set -x
set -e

target=$1
out_file=$2
threads=$3
branchname=$4

# this is a special file that is parsed by Azure Devops
result_file="../result.txt"

build_home="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
. "$build_home"/build_funs.sh

export_home KRML "$(pwd)/karamel"
export_home FSTAR "$(pwd)/FStar"

cd karamel
rootPath=$(pwd)
exec_build
cd ..

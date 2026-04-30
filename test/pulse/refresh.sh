#!/bin/bash

# Refresh the outputs from F* nightly.

curl -L https://aka.ms/install-fstar | bash -s -- --nightly --dest local-fstar --no-link
cleanup () {
	rm -rf local-fstar
}
trap cleanup EXIT ERR

FSTAR_EXE=$(pwd)/local-fstar/bin/fstar.exe make clean
FSTAR_EXE=$(pwd)/local-fstar/bin/fstar.exe make -j$(nproc) accept

echo "Done!"
exit 0

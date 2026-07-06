#!/bin/bash

# Refresh the outputs from F* nightly.

if ! [ -d local-fstar ]; then
  curl -L https://aka.ms/install-fstar | bash -s -- --nightly --dest local-fstar --no-link
fi

# Invalidate existing karamel files
touch -c _output/*.krml
FSTAR_EXE=$(pwd)/local-fstar/bin/fstar.exe make -j$(nproc) accept -k
RES=$?

if [ $RES -eq 0 ]; then
  echo "Done!"
  exit 0
else
  echo "error: there were some failures regenerating the expected C files" >&2
  exit 1
fi

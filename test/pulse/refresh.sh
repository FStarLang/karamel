#!/bin/bash

# Refresh the outputs from F* nightly.
# Run as MAKE=gmake ./refresh.sh from MacOS

if ! [ -d local-fstar ]; then
  curl -L https://aka.ms/install-fstar | bash -s -- --nightly --dest local-fstar --no-link
fi

export FSTAR_EXE="$(pwd)/local-fstar/bin/fstar.exe"

# .depend contains absolute paths to the F* installation. Regenerate it and
# the checked/extracted files so they all use the local F* version.
"${MAKE:-make}" clean || exit $?
"${MAKE:-make}" -j$(nproc) accept -k
RES=$?

if [ $RES -eq 0 ]; then
  echo "Done!"
  exit 0
else
  echo "error: there were some failures regenerating the expected C files" >&2
  exit 1
fi

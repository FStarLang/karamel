KreMLin
-------

[![Build Status](https://travis-ci.org/FStarLang/kremlin.svg?branch=master)](https://travis-ci.org/FStarLang/kremlin)

Transforms a subset of F* into C code. See the [ML Workshop
Paper](https://jonathan.protzenko.fr/papers/ml16.pdf) for more information.

## Trying out KreMLin

Make sure you run `opam update` to get `process-0.2.1` (version `0.2` doesn't
work on Windows). Install all of the packages below, possibly following
instructions from https://github.com/FStarLang/FStar/wiki for "difficult"
packages (e.g. `ppx_deriving`) on Windows.

`opam install ppx_deriving_yojson zarith pprint menhir ulex process fix`

To build just run `make` from this directory.

If you have the latest version of F* (make sure `fstar.exe` is in your
path) then you can run the KreMLin test suite by doing `make test`.

File a bug if things don't work!

## License

This new variant of F* is released under the [Apache 2.0 license];
see `LICENSE` for more details.

[Apache 2.0 license]: https://www.apache.org/licenses/LICENSE-2.0

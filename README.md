KreMLin
-------

[![Build Status](https://travis-ci.org/FStarLang/kremlin.svg?branch=master)](https://travis-ci.org/FStarLang/kremlin)

Transforms a subset of F* into C code. See the [ML Workshop
Paper](https://jonathan.protzenko.fr/papers/ml16.pdf) for more information.

## Build

Just run `make` from this directory. The test suite (`make test`) requires the
latest version of F*.

## License

This new variant of F* is released under the [Apache 2.0 license];
see `LICENSE` for more details.

[Apache 2.0 license]: https://www.apache.org/licenses/LICENSE-2.0

## Installation

Make sure you run `opam update` to get `process-0.2.1` (version `0.2` doesn't
work on Windows). Install all of the packages below, possibly following
instructions from https://github.com/FStarLang/FStar/wiki for "difficult"
packages (e.g. `ppx_deriving`) on Windows.

`opam install ppx_deriving_yojson zarith pprint menhir ulex process fix`

Make sure `fstar.exe` is in your path. Run `make`.

File a bug if things don't work!

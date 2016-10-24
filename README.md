KreMLin
-------

[![Build Status](https://travis-ci.org/FStarLang/kremlin.svg?branch=master)](https://travis-ci.org/FStarLang/kremlin)

Transforms a subset of F* into C code. See the [ML Workshop Paper] for
more information, or DESIGN.md for some draft notes.

[ML Workshop Paper]: https://jonathan.protzenko.fr/papers/ml16.pdf

## Trying out KreMLin

Make sure you run `opam update` first, so that by running the `opam install`
command below you get `process-0.2.1` (`process` version `0.2` doesn't work on
Windows). Install all of the packages below, on Windows possibly following
instructions from https://github.com/protz/ocaml-installer/wiki for "difficult"
packages (e.g. `ppx_deriving`).

`$ opam install ppx_deriving_yojson zarith pprint menhir ulex process fix`

To build just run `make` from this directory.

The WebASM branch uses a new package. If you're not running Windows:

```
$ opam repository add jonathan git+https://github.com/msprotz/opam-repository
$ opam install wasm
```

If you're running Windows:

```
$ git clone https://github.com/WebAssembly/spec
$ cd spec/interpreter
$ mv aux foo
$ sed -i s/aux/foo _tags Makefile
$ make install
```

If you have the latest version of F* and `fstar.exe` is in your `PATH` then you
can run the KreMLin test suite by doing `make test`.

File a bug if things don't work!

## Documentation

The simple example from the [ML Workshop Paper] is available in
`test/ML16.fst` and you can compile it with `make ML16.exe`.

Also check out the `--help` flag:
```
$ _build/src/Kremlin.native --help
```

## License

Kremlin is released under the [Apache 2.0 license]; see `LICENSE` for more details.

[Apache 2.0 license]: https://www.apache.org/licenses/LICENSE-2.0

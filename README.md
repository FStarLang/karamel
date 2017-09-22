KreMLin
-------

[![Build Status](https://travis-ci.org/FStarLang/kremlin.svg?branch=master)](https://travis-ci.org/FStarLang/kremlin)

KreMLin is a tool that extracts an F\* program to readable C code. If the F\*
program verifies against a low-level memory model that talks about the stack and
the heap; if it is first-order; if it obeys certain restrictions (e.g.
non-recursive data types) then KreMLin will turn it into C.
- [DESIGN.md](DESIGN.md) has a technical overview of the different
  transformation passes performed by KreMLin
- [MANUAL.md](MANUAL.md) contains some tips&tricks when working with KreMLin.

This work has been formalized on paper. We state that the compilation of
such F\* programs to C preserves semantics. We start from Low\*, a subset of
F\*, and relate its semantics to [CompCert](http://compcert.inria.fr/)'s Clight.
- the [ICFP 2017 Paper] provides an overview of KreMLin as well
  as a paper formalization of our compilation toolchain

We have written 20,000 lines of low-level F\* code, implementing the [TLS
1.3](https://tlswg.github.io/tls13-spec/) record layer. As such, KreMLin is a
key component of [Project Everest](https://project-everest.github.io/).
- [HACL*], our High Assurance Crypto Library, provides numerous cryptographic
  primitives written in F\*; these primitives enjoy memory safety, functional
  correctness, and some degree of side-channel resistance -- they extract to C
  via KreMLin.

[ML Workshop Paper]: https://jonathan.protzenko.fr/papers/ml16.pdf
[HACL*]: https://github.com/mitls/hacl-star/
[ICFP 2017 Paper]: https://arxiv.org/abs/1703.00053

## Trying out KreMLin

Make sure you run `opam update` first, so that by running the `opam install`
command below you get `process-0.2.1` (`process` version `0.2` doesn't work on
Windows). Install all of the packages below, on Windows possibly following
instructions from https://github.com/protz/ocaml-installer/wiki for "difficult"
packages (e.g. `ppx_deriving`).

`$ opam install ppx_deriving_yojson zarith pprint menhir ulex process fix wasm`

To build just run `make` from this directory.

If you have the latest version of F* and `fstar.exe` is in your `PATH` then you
can run the KreMLin test suite by doing `make test`.

File a bug if things don't work!

## Documentation

The simple example from the [ML Workshop Paper] is available in
`test/ML16.fst` and you can compile it with `make ML16.exe`.

Also check out the `--help` flag:
```
$ ./krml --help
```

## License

Kremlin is released under the [Apache 2.0 license]; see `LICENSE` for more details.

[Apache 2.0 license]: https://www.apache.org/licenses/LICENSE-2.0

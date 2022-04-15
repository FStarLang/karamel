# Tests for KaRaMeL

`make standalone` will generate a series of unit tests that can be run with a
sole dependency on the F\* binary and its standard libraries.

`make extra` requires a source checkout of F\*. It compiles some cryptographic
code, but the bulk of the testing is done elsewhere (see [project
everest](https://github.com/project-everest/everest-ci)).

## WASM backend

This is all super experimental. Roughly, compile V8 from source (good luck).
Then:

```bash
$ make Crypto.Symmetric.Chacha20.wasm
$ cd Crypto.Symmetric.Chacha20.out
$ ../path/to/d8 d8.js
```

Alternatively, replace the call to `d8` with:

```bash
$ npm install -g http-server
$ http-server .
```

Then, use Chrome Canary 58 (success on OSX, failure on Windows) and navigate to
`localhost:8080`. Currently, this prints out a bunch of stuff in the developer
console (open it first).

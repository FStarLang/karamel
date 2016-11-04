# A minimalistic Makefile for calling Kremlin... KOPTS is for user-defined flags
# (e.g. KOPTS="-cc clang -ccopt -fsanitize=undefined,address -ccopt -Wno-non-literal-null-conversion -Wno-unused-value")
CRYPTO	= FSTAR_HOME/examples/low-level/crypto
OPTS	= -I $(CRYPTO) -I $(CRYPTO)/real $(KOPTS)
TESTOPTS= -add-include '"testlib.h"' -I . testlib.c
KRML	= ../krml

all: Hoisting.exe Flat.exe Renaming.exe Vla.exe Inline.exe \
  Private.exe ML16.exe Abbrev.exe TSet.exe Tuples.exe \
  DataTypesSimple.exe DataTypes.exe Parameterized.exe \
  Scope.exe Crypto.Symmetric.Chacha20.exe \
  Crypto.KrmlTest.exe

broken: Crypto.Symmetric.Poly1305.exe Mutable.exe 

# Standalone test files that have a main in F* (hence -no-prefix)
%.exe: %.fst
	$(KRML) $(OPTS) $(TESTOPTS) $(EXTRA) -tmpdir $(subst .exe,.out,$@) -no-prefix $* -o $@ $<
	./$@

ML16.exe: EXTRA = ml16-native.c
Scope.exe: EXTRA = -ccopt -O3

# Test files that have an "external" main written by hand...
Crypto.%.exe:
	$(KRML) $(OPTS) $(EXTRA) -tmpdir $(subst .exe,.out,$@) -o $@ $(subst .exe,.fst,$@)
	./$@

Crypto.Symmetric.Poly1305.exe: EXTRA = main-Poly1305.c testlib.c
Crypto.Symmetric.Chacha20.exe: EXTRA = main-Chacha.c testlib.c
Crypto.AEAD.Chacha20Poly1305.exe: EXTRA = main-Aead.c testlib.c
Crypto.KrmlTest.exe: EXTRA = $(CRYPTO)/test_hacks.c -no-prefix Crypto.KrmlTest $(TESTOPTS) -ccopt -Wno-error=pointer-sign

SimpleWasm.wasm: SimpleWasm.fst
	$(KRML) $(OPTS) -verbose $^ -o $@ -wasm

clean:
	rm -rf *.exe *.dSYM *.out

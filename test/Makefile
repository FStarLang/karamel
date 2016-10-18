# A minimalistic Makefile for calling Kremlin... KOPTS is for user-defined flags
# (e.g. -verbose).
CRYPTO=FSTAR_HOME/examples/low-level/crypto
OPTS=-I $(CRYPTO) -I $(CRYPTO)/real $(KOPTS)
TESTOPTS=$(OPTS) -add-include '"testlib.h"' -I . testlib.c
KRML=../krml

all: Hoisting.exe Flat.exe Renaming.exe Vla.exe Inline.exe \
  Private.exe ML16.exe Abbrev.exe TSet.exe Tuples.exe \
  DataTypesSimple.exe \
  Crypto.Symmetric.Poly1305.exe Crypto.Symmetric.Chacha20.exe

broken: Mutable.exe Aead.exe

# Standalone test files that have a main in F* (hence -no-prefix)
%.exe: %.fst
	$(KRML) $(TESTOPTS) $(EXTRA) -tmpdir $(subst .exe,-out,$@) -no-prefix $* -o $@ $<
	./$@

ML16.exe: EXTRA = ml16-native.c

# Test files that have an "external" main written by hand...
Crypto.%.exe:
	$(KRML) $(OPTS) $(EXTRA) -tmpdir $(subst .exe,-out,$@) -o $@ $(subst .exe,.fst,$@)
	./$@

Crypto.Symmetric.Poly1305.exe: EXTRA = main-Poly1305.c testlib.c
Crypto.Symmetric.Chacha20.exe: EXTRA = main-Chacha.c testlib.c

Aead.exe: EXTRA = main-Aead.c testlib.c

SimpleWasm.wasm: SimpleWasm.fst
	$(KRML) $(OPTS) -verbose $^ -o $@ -wasm

clean:
	rm -rf *.exe

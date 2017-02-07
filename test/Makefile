# A minimalistic Makefile for calling Kremlin... KOPTS is for user-defined flags
# (e.g. KOPTS="-cc clang -ccopt -fsanitize=undefined,address -ccopt -Wno-non-literal-null-conversion -Wno-unused-value")
CRYPTO		= FSTAR_HOME/examples/low-level/crypto
CRYPTO_OPTS	= -I $(CRYPTO) -I $(CRYPTO)/real
TEST_OPTS	= -add-include '"testlib.h"' -I . ../kremlib/testlib.c
KRML		= ../krml

all: standalone extra

# Tests that do not need a source checkout of F* to run
standalone: Hoisting.exe Flat.exe Renaming.exe Vla.exe Inline.exe \
  Private.exe ML16.exe Abbrev.exe TSet.exe Tuples.exe \
  DataTypesSimple.exe DataTypes.exe Parameterized.exe \
  Scope.exe Attributes.exe Unsound.exe

extra: Crypto.Symmetric.Chacha20.exe

# Standalone test files that have a main in F* (hence -no-prefix)
%.exe: %.fst
	$(KRML) $(KOPTS) $(TEST_OPTS) $(EXTRA) -tmpdir $(subst .exe,.out,$@) -no-prefix $* -o $@ $<
	./$@

ML16.exe: EXTRA = ml16-native.c
Scope.exe: EXTRA = -ccopt -O3
Crypto.Symmetric.Chacha20.exe: EXTRA=$(CRYPTO_OPTS) main-Chacha.c

.PHONY: Crypto.Symmetric.Chacha20.fst

%.wasm: %.fst
	$(KRML) $(KOPTS) $(TEST_OPTS) $(EXTRA) -tmpdir $(subst .exe,.out,$@) $^ -wasm -drop Prims -drop FStar

Crypto.Symmetric.Chacha20.wasm: EXTRA=$(CRYPTO_OPTS)

clean:
	rm -rf *.exe *.dSYM *.out *.wasm

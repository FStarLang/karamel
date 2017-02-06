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

# Test files that have an "external" main written by hand...
Crypto.%.exe:
	$(KRML) $(KOPTS) $(CRYPTO_OPTS) $(EXTRA) -tmpdir $(subst .exe,.out,$@) -o $@ $(subst .exe,.fst,$@)
	./$@

Crypto.Symmetric.Chacha20.exe: EXTRA = main-Chacha.c

# Wasm tests
%.wasm: %.fst
	$(KRML) $(KOPTS) $(TEST_OPTS) $(EXTRA) $^ -wasm -tmpdir $(subst .wasm,.out,$@) -drop Prims -drop FStar
	cp $*.out/$@ .

Crypto.%.wasm:
	$(KRML) $(KOPTS) $(CRYPTO_OPTS) $(EXTRA) $(subst .wasm,.fst,$@) -wasm -tmpdir $(subst .wasm,.out,$@) -drop Prims -drop FStar

clean:
	rm -rf *.exe *.dSYM *.out *.wasm

# A minimalistic Makefile for calling Kremlin... KOPTS is for user-defined flags
# (e.g. KOPTS="-cc clang -ccopt -fsanitize=undefined,address -ccopt -Wno-non-literal-null-conversion -Wno-unused-value")
CRYPTO		= FSTAR_HOME/examples/low-level/crypto
CRYPTO_OPTS	= -I $(CRYPTO) -I $(CRYPTO)/real
TEST_OPTS	= -add-include '"testlib.h"' -I . ../kremlib/testlib.c -warn-error @4
KRML_BIN	= ../_build/src/Kremlin.native
KRML		= $(KRML_BIN) $(KOPTS) $(TEST_OPTS)
FILES		= \
  Hoisting.exe Flat.exe Renaming.exe Vla.exe Inline.exe \
  Private.exe ML16.exe Abbrev.exe Tuples.exe \
  DataTypesSimple.exe DataTypes.exe Parameterized.exe \
  Scope.exe Attributes.exe Unsound.exe Substitute.exe \
  InlineTest.exe Ghost1.exe Loops.exe Structs.exe \
  Recursive.exe RecursivePoly.exe Structs2.exe StringLit.exe \
  FunctionalEncoding.exe FunPtr.exe Test128.exe \
  CheckedInt.exe Polymorphic.exe MutualDatatypes.exe \
  CheckedInt.exe Polymorphic.exe GcTypes.exe BadMatch.exe C89.exe \
  PatternAny.exe MutualDatatypesPolyIndex.exe \
EXTRA_FILES	= \
  Crypto.Symmetric.Chacha20.exe
WASM_FILES	= \
  Crypto.Symmetric.Chacha20.wasm WasmTrap.wasm
BROKEN		= \
  HigherOrder.exe

all: standalone extra

# The standalone tests don't need a source checkout of F* to run
standalone: $(FILES) $(subst .exe,.krml,$(FILES))
extra: $(EXTRA_FILES) $(subst .exe,.krml,$(EXTRA_FILES))
wasm: $(WASM_FILES) $(subst .wasm,.krml,$(EXTRA_FILES))

%.krml: %.fst
	$(KRML) $(EXTRA) -tmpdir $(subst .krml,.out,$@) -skip-translation $<
	cp $(subst .krml,.out,$@)/out.krml $@

%.exe: %.krml $(KRML_BIN)
	$(KRML) $(EXTRA) -tmpdir $(subst .exe,.out,$@) -no-prefix $* -o $@ $<
	./$@

%.wasm: EXTRA += -wasm
%.wasm: %.krml $(KRML_BIN)
	$(KRML) $(EXTRA) -tmpdir $(subst .wasm,.out,$@) $(JSFILES) -no-prefix $* $<
	cp $(wildcard ../kremlib/js/*.js) $(JSFILES) $(subst .wasm,.out,$@)
	cd $*.out && $(shell which d8) main.js
	# cd $*.out && ch -Wasm main.js

Structs2.exe: EXTRA = -wasm -d force-c -drop C,TestLib wasm-stubs.c
ML16.exe: EXTRA = ml16-native.c
Scope.exe: EXTRA = -ccopt -O3
Test128.exe: EXTRA = -fnouint128 -static-header FStar
Crypto.Symmetric.Chacha20.exe: EXTRA+=$(CRYPTO_OPTS) main-Chacha.c
HigherOrder.exe: EXTRA = -warn-error +9
Crypto.Symmetric.Chacha20.exe: EXTRA=$(CRYPTO_OPTS) main-Chacha.c
C89.exe: EXTRA = -ccopts -Wno-long-long,-Wno-format,-pedantic -fc89

.PHONY: Crypto.Symmetric.Chacha20.fst

Crypto.Symmetric.Chacha20.wasm: JSFILES=main-Chacha.js
Crypto.Symmetric.Chacha20.wasm: EXTRA+=$(CRYPTO_OPTS) -drop FStar

clean:
	rm -rf *.exe *.dSYM *.out *.wasm *.krml

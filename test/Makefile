# A minimalistic Makefile for calling Kremlin... KOPTS is for user-defined flags
# (e.g. KOPTS="-cc clang -ccopt -fsanitize=undefined,address -ccopt -Wno-non-literal-null-conversion -Wno-unused-value")
READLINK	= $(shell which greadlink >/dev/null 2>&1 && echo greadlink || echo readlink)
CRYPTO		= $(FSTAR_HOME)/examples/low-level/crypto
SALSA		= $(HACL_HOME)/code/salsa-family
CURVE		= $(HACL_HOME)/code/curve25519
ED		= $(HACL_HOME)/code/ed25519
POLY		= $(HACL_HOME)/code/poly1305
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
  CheckedInt.exe Polymorphic.exe GcTypes.exe BadMatch.exe C89.exe \
  PatternAny.exe Debug.exe hello-system/HelloSystem.exe Server.exe \
  ExitCode.exe
EXTRA_FILES	= \
  $(CRYPTO)/Crypto.Symmetric.Chacha20.exe
WASM_FILES	= \
  WasmTrap.wasm Wasm1.wasm Wasm2.wasm Wasm3.wasm
WASM_EXTRA	= \
  $(SALSA)/Hacl.Test.Chacha20.wasm $(CURVE)/Hacl.Test.X25519.wasm \
  $(POLY)/Hacl.Test.Poly1305_64.wasm $(ED)/Hacl.Test.Ed25519.wasm
# One can define NEGATIVE=true for wasm targets that are negative tests
NEGATIVE	= false
# Chacha20: need to pass StackInline information properly
# HigherOrder: need to implement "natural arity" tracking
BROKEN		= \
  $(CRYPTO)/Crypto.Symmetric.Chacha20.wasm HigherOrder.exe

all: standalone extra
wasm: wasm-standalone wasm-extra

# The standalone tests don't need a source checkout of F* to run
standalone: $(FILES) $(subst .exe,.krml,$(FILES))
extra: $(EXTRA_FILES) $(subst .exe,.krml,$(EXTRA_FILES))
wasm-standalone: $(WASM_FILES)
wasm-extra: $(WASM_EXTRA)

.PRECIOUS: %.krml

# A common target to produce a .krml file
%.krml: %.fst
	$(KRML) $(EXTRA) -tmpdir $(subst .krml,.out,$@) -skip-translation $<
	cp $(subst .krml,.out,$@)/out.krml $@

# Then, from there on, a specific target for native C compilation
%.exe: %.krml $(KRML_BIN)
	$(KRML) $(EXTRA) -tmpdir $(subst .exe,.out,$@) -no-prefix $(notdir $*) -o $@ $<
	$$($(READLINK) -f $@)

# Various flags to be passed to some targets...
Structs2.exe: EXTRA = -wasm -d force-c -drop C,TestLib wasm-stubs.c
ML16.exe: EXTRA = ml16-native.c
Scope.exe: EXTRA = -ccopt -O3
Test128.exe: EXTRA = -fnouint128 -static-header FStar
HigherOrder.exe: EXTRA = -warn-error +9
C89.exe: EXTRA = -ccopts -Wno-long-long,-Wno-format,-pedantic -fc89
Debug.exe: EXTRA = -d c-calls
Server.exe: EXTRA = -add-include '"kremstr.h"' main-Server.c
$(CRYPTO)/Crypto.Symmetric.Chacha20.exe: EXTRA+=$(CRYPTO_OPTS) main-Chacha.c
hello-system/HelloSystem.exe: EXTRA = -add-include '"system.h"' \
	hello-system/system.c -I hello-system -no-prefix SystemNative \
	-drop SystemNative -add-include '<netdb.h>'

# A target for WASM compilation. All WASM targets get the -wasm flag;
# some specific targets may override NEGATIVE for negative tests.
%.wasm: EXTRA += -wasm
%.wasm: %.krml $(KRML_BIN)
	$(KRML) $(EXTRA) -tmpdir $(subst .wasm,.out,$@) $(JSFILES) -no-prefix $(notdir $*) $<
	cd $*.out && \
	  if ! $(NEGATIVE); then $(shell which d8) main.js; \
	  else ! $(shell which d8) main.js; fi && \
	  cd .. && cp $*.out/$(subst .,_,$(notdir $(basename $@))).wasm $@
	# cd $*.out && ch -Wasm main.js

# Customizing some WASM targets.
$(CRYPTO)/Crypto.Symmetric.Chacha20.wasm: JSFILES=main-Chacha.js
$(CRYPTO)/Crypto.Symmetric.Chacha20.wasm: EXTRA+=$(CRYPTO_OPTS) -drop FStar
WasmTrap.wasm: NEGATIVE = true

# External WASM targets: recycle the HACL* Makefile!
HACL_DROP=Prims,Hacl.UInt8,Hacl.UInt16,Hacl.UInt32,Hacl.UInt64,Hacl.UInt128,Hacl.Endianness,Hacl.Cast,Hacl.Spec.*,Spec.*,Seq.*

.PHONY: $(SALSA)/Hacl.Test.Chacha20.krml
$(SALSA)/Hacl.Test.Chacha20.krml:
	KREMLIN_ARGS=-wasm $(MAKE) -C $(SALSA) chacha-c/out.krml
	[ -e $(subst .krml,.out,$@) ] || ln -sf $(SALSA)/chacha-c $(subst .krml,.out,$@)
	cp $(subst .krml,.out,$@)/out.krml $@

$(SALSA)/Hacl.Test.Chacha20.wasm: EXTRA+=-drop $(HACL_DROP) \
  -bundle 'Chacha20=Hacl.Impl.*,Chacha20,Hacl.Lib.*'

.PHONY: $(CURVE)/Hacl.Test.X25519.krml
$(CURVE)/Hacl.Test.X25519.krml:
	KREMLIN_ARGS=-wasm $(MAKE) -C $(CURVE) extract-c
	[ -e $(subst .krml,.out,$@) ] || ln -sf $(CURVE)/x25519-c $(subst .krml,.out,$@)
	cp $(subst .krml,.out,$@)/out.krml $@

$(CURVE)/Hacl.Test.X25519.wasm: EXTRA+=-drop $(HACL_DROP) \
  -bundle 'Curve25519=Hacl.Bignum,Hacl.Bignum.*,Hacl.EC,Hacl.EC.*'

.PHONY: $(POLY)/Hacl.Test.Poly1305_64.krml
$(POLY)/Hacl.Test.Poly1305_64.krml:
	KREMLIN_ARGS=-wasm $(MAKE) -C $(POLY) poly-c/out.krml
	[ -e $(subst .krml,.out,$@) ] || ln -sf $(POLY)/poly-c $(subst .krml,.out,$@)
	cp $(subst .krml,.out,$@)/out.krml $@

$(POLY)/Hacl.Test.Poly1305_64.wasm: EXTRA+=-drop $(HACL_DROP) \
  -bundle 'Poly1305_64=Hacl.Bignum.*,Hacl.Impl.*,Hacl.Standalone.*,Poly1305_64' \
  -drop AEAD_Poly1305_64

.PHONY: $(ED)/Hacl.Test.Ed25519.krml
$(ED)/Hacl.Test.Ed25519.krml:
	KREMLIN_ARGS=-wasm $(MAKE) -C $(ED) ed25519-c/out.krml
	[ -e $(subst .krml,.out,$@) ] || ln -sf $(ED)/ed25519-c $(subst .krml,.out,$@)
	cp $(subst .krml,.out,$@)/out.krml $@

$(ED)/Hacl.Test.Ed25519.wasm: EXTRA+=-drop $(HACL_DROP) \
  -bundle 'Ed25519=Ed25519,Hacl.EC,Hacl.EC.*,Hacl.Impl.*,Hacl.Lib.*,Hacl.Bignum.*,Hacl.Bignum25519,Hacl.Bignum,Hacl.Spec.*,SHA2_512,Hacl.Hash.*' \

clean:
	rm -rf *.exe *.dSYM *.out *.wasm *.krml web

web: wasm
	mkdir -p $@
	echo "<h1>WHACL* -- Web HACL*</h1><ul>" > $@/index.html
	for a in $(SALSA)/chacha-c $(CURVE)/x25519-c $(POLY)/poly-c $(ED)/ed25519-c; do \
	  cp -R $$a web; \
	  echo "<li><a href=\"$$(basename $$a)/main.html\">$$(basename $$a)</a>" >> $@/index.html; \
	done

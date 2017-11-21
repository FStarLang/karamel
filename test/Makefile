# A minimalistic Makefile for calling Kremlin... KOPTS is for user-defined flags
# (e.g. KOPTS="-cc clang -ccopt -fsanitize=undefined,address -ccopt -Wno-non-literal-null-conversion -Wno-unused-value")
READLINK	= $(shell which greadlink >/dev/null 2>&1 && echo greadlink || echo readlink)
CRYPTO		= $(FSTAR_HOME)/examples/low-level/crypto
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
  ExitCode.exe DataTypesMut.exe ParamAbbrev.exe Null.exe Failwith.exe \
  CustomEq.exe TestKremBytes.exe
EXTRA_FILES	= \
  $(CRYPTO)/Crypto.Symmetric.Chacha20.exe
WASM_FILES	= \
  WasmTrap.wasm Wasm1.wasm Wasm2.wasm Wasm3.wasm
NEGATIVE	= false
# Chacha20: need to pass StackInline information properly
# HigherOrder: need to implement "natural arity" tracking
BROKEN		= \
  $(CRYPTO)/Crypto.Symmetric.Chacha20.wasm HigherOrder.exe
WEB_DIR		?= web

all: standalone extra
wasm: wasm-standalone wasm-extra
external: hacl-test
everything: all wasm external

# The standalone tests don't need a source checkout of F* to run
standalone: $(FILES) $(subst .exe,.krml,$(FILES))
extra: $(EXTRA_FILES) $(subst .exe,.krml,$(EXTRA_FILES))
wasm-standalone: $(WASM_FILES)
wasm-extra: hacl-algs

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
StringLit.exe: EXTRA = ../kremlib/kremstr.c -add-include '"kremstr.h"'
Failwith.exe: EXTRA = -add-include '"kremstr.h"'
FunctionalEncoding.exe: EXTRA = -add-include '"kremstr.h"'
CustomEq.exe: EXTRA = customeq_native.c
$(CRYPTO)/Crypto.Symmetric.Chacha20.exe: EXTRA+=$(CRYPTO_OPTS) main-Chacha.c
hello-system/HelloSystem.exe: EXTRA = -add-include '"system.h"' \
	hello-system/system.c -I hello-system -no-prefix SystemNative \
	-drop SystemNative -add-include '<netdb.h>'
TestKremBytes.exe: EXTRA = -add-include '"krembytes.h"' -add-include \
	'"kremstr.h"' -drop FStar.Bytes -d reachability

# External C tests that leverage other projects.
.PHONY: hacl-test
hacl-test:
	$(MAKE) -C $(HACL_HOME)/secure_api krml-test-hacl.exe
	$(HACL_HOME)/secure_api/krml-test-hacl.exe

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
HACL_DROP=Prims,Hacl.UInt8,Hacl.UInt16,Hacl.UInt32,Hacl.UInt64,Hacl.UInt128,Hacl.Endianness,Hacl.Cast,Hacl.Spe.*,Hacl.Spec.*,Spec.*,Seq.*
HACL_ALGS=CHACHA SALSA CURVE POLY ED HMAC

# Arguments to the meta-rule
CHACHA=$(HACL_HOME)/code/salsa-family
CHACHA_DIR=chacha-c
CHACHA_TEST=Hacl.Test.Chacha20.krml
CHACHA_ARGS=-bundle 'Chacha20=Hacl.Impl.*,Chacha20,Hacl.Lib.*'

SALSA=$(HACL_HOME)/code/salsa-family
SALSA_DIR=salsa-c
SALSA_TEST=Hacl.Test.Salsa20.krml
SALSA_ARGS=-bundle 'Salsa20=Salsa20,Hacl.Impl.*,Hacl.Lib.*'

CURVE=$(HACL_HOME)/code/curve25519
CURVE_DIR=x25519-c
CURVE_TEST=Hacl.Test.X25519.krml
CURVE_ARGS=-bundle 'Curve25519=Hacl.Bignum,Hacl.Bignum.*,Hacl.EC,Hacl.EC.*'

POLY=$(HACL_HOME)/code/poly1305
POLY_DIR=poly-c
POLY_TEST=Hacl.Test.Poly1305_64.krml
POLY_ARGS=-bundle 'Poly1305_64=Hacl.Bignum.*,Hacl.Impl.*,Hacl.Standalone.*,Poly1305_64' \
  -drop AEAD_Poly1305_64

ED=$(HACL_HOME)/code/ed25519
ED_DIR=ed25519-c
ED_TEST=Hacl.Test.Ed25519.krml
ED_ARGS=-bundle 'Ed25519=Ed25519,Hacl.EC,Hacl.EC.*,Hacl.Impl.*,Hacl.Lib.*,Hacl.Bignum.*,Hacl.Bignum25519,Hacl.Bignum,Hacl.Spec.*,SHA2_512,Hacl.Hash.*' \

HMAC=$(HACL_HOME)/code/hmac
HMAC_DIR=hmac-c
HMAC_TEST=Hacl.Test.HMAC.SHA2_256.krml
HMAC_ARGS=-bundle 'HMAC_SHA2_256=Hacl.Hash.Lib.Create,Hacl.Hash.Lib.LoadStore,Hacl.Hash.SHA2_256,Hacl.HMAC.SHA2_256,HMAC_SHA2_256'

# A template that uses the global namespace as an associative array. Note:
# equals sign is not Make 3.81-compatible (last GPLv2 version on OSX).
define HACL_template
.PHONY: $$($(1))/$$($(1)_TEST)
$$($(1))/$$($(1)_TEST):
	KREMLIN_ARGS=-wasm $$(MAKE) -C $$($(1)) $$($(1)_DIR)/out.krml
	[ -e $$(subst .krml,.out,$$@) ] || ln -sf $$($(1))/$$($(1)_DIR) $$(subst .krml,.out,$$@)
	cp $$(subst .krml,.out,$$@)/out.krml $$@

$$($(1))/$$(subst .krml,.wasm,$$($(1)_TEST)): EXTRA+=-drop $$(HACL_DROP) $$($(1)_ARGS)
hacl-algs: $$($(1))/$$(subst .krml,.wasm,$$($(1)_TEST))

clean-$(1):
	$(MAKE) -C $$($1) clean
clean-hacl: clean-$(1)

web-$(1): web-head $$($(1))/$$(subst .krml,.wasm,$$($(1)_TEST))
	cp -R $$($(1))/$$($(1)_DIR) $$(WEB_DIR)/
	echo "<li><a href=\"$$($(1)_DIR)/main.html\">$$($(1)_DIR)</a>" >> $(WEB_DIR)/index.html
web-body: web-$(1)
endef

# Evaluate the meta-rule for each algorithm.
$(foreach alg,$(HACL_ALGS),$(eval $(call HACL_template,$(alg))))

clean:
	rm -rf *.exe *.dSYM *.out *.wasm *.krml $(WEB_DIR)

distclean: clean clean-hacl
	$(MAKE) -C $(HACL_HOME)/secure_api clean

# Generation of a mini-website
web-head:
	mkdir -p $(WEB_DIR)
	echo "<h1>WHACL* -- Web HACL*</h1><ul>" > $(WEB_DIR)/index.html

web-body: web-head

$(WEB_DIR): web-body

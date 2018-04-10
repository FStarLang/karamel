CRYPTO		= $(FSTAR_HOME)/examples/low-level/crypto
CRYPTO_OPTS	= -I $(CRYPTO) -I $(CRYPTO)/real
TEST_OPTS	= -add-include '"testlib.h"' -I . ../kremlib/testlib.c -warn-error @4
KRML_BIN	= ../_build/src/Kremlin.native
KRML		= $(KRML_BIN) $(KOPTS) $(TEST_OPTS)
FILES		= \
  TestKremBytes.test Hoisting.test Flat.test Renaming.test Vla.test Inline.test \
  Private.test ML16.test Abbrev.test Tuples.test \
  DataTypesSimple.test DataTypes.test Parameterized.test \
  Scope.test Attributes.test Unsound.test Substitute.test \
  InlineTest.test Ghost1.test Loops.test Structs.test \
  TotalLoops.test \
  Recursive.test RecursivePoly.test Structs2.test StringLit.test \
  FunctionalEncoding.test FunPtr.test Test128.test \
  CheckedInt.test Polymorphic.test GcTypes.test BadMatch.test C89.test \
  PatternAny.test Debug.test hello-system/HelloSystem.test Server.test \
  ExitCode.test DataTypesMut.test ParamAbbrev.test Null.test Failwith.test \
  CustomEq.test Uu.test WildCard.test UnusedParameter.test EqB.test MutRec.test \
  MallocFree.test TestAlloca.test OptimizedOption.test PushPop.test EtaStruct.test \
  Verbatim.test Const.test $(CRYPTO)/Crypto.Symmetric.Chacha20.test Uu.test \
  LinkedList1.test NoExtract.test InlineNoExtract.test
CUSTOM		= count-uu
WASM_FILES	= \
  WasmTrap.wasm-test Wasm1.wasm-test Wasm2.wasm-test Wasm3.wasm-test
NEGATIVE	= false
# Chacha20: need to pass StackInline information properly
# HigherOrder: need to implement "natural arity" tracking
BROKEN		= \
  $(CRYPTO)/Crypto.Symmetric.Chacha20.wasm HigherOrder.exe
WEB_DIR		?= web
CACHE_DIR	= .cache
OUTPUT_DIR	= .output
HINTS_DIR	= .hints
FSTAR		= fstar.exe --cache_checked_modules --use_two_phase_tc true \
  --cache_dir $(CACHE_DIR) --odir $(OUTPUT_DIR) \
  --include hello-system --include ../kremlib --include ../runtime \
  --include $(CRYPTO) --use_hints --record_hints --hint_info

# This just needs F* + KreMLin
all: $(FILES) $(CUSTOM)

# Needs d8
wasm: $(WASM_FILES)

# Needs a checkout of HACL*
external: hacl-test hacl-algs

# All of the above
everything: all wasm external

.PRECIOUS: %.krml

# Use F*'s dependency mechanism and fill out the missing rules.

.depend: $(subst .wasm-test,.fst,$(WASM_FILES)) $(subst .test,.fst,$(FILES)) | Makefile
	$(FSTAR) --dep full $^ ../runtime/WasmSupport.fst --extract Kremlin > .depend

-include .depend

$(HINTS_DIR):
	mkdir -p $@

$(CACHE_DIR)/%.checked: | .depend $(HINTS_DIR)
	$(FSTAR) --hint_file $(HINTS_DIR)/$*.hints $<
	touch $@

$(OUTPUT_DIR)/%.krml: | .depend
	$(FSTAR) --codegen Kremlin \
	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	  $(notdir $(subst .checked,,$<))
	touch $@

$(OUTPUT_DIR)/%.exe: $(OUTPUT_DIR)/FStar_UInt128.krml | $(KRML_BIN)
	$(KRML) $(EXTRA) -tmpdir $(subst .exe,.out,$@) -no-prefix $(notdir $*) \
	  -o $@ $(filter-out $(OUTPUT_DIR)/prims.krml,$^)

.SECONDEXPANSION:
%.test: $(OUTPUT_DIR)/$$(notdir $$(subst .,_,$$*)).exe
	@$^ && echo "\033[01;32m✔\033[00m [TEST,$*]" || echo "\033[01;31m✘\033[00m [TEST,$*]"

# Various flags to be passed to some targets...
$(OUTPUT_DIR)/Structs2.exe: EXTRA = -wasm -d force-c -drop C,TestLib wasm-stubs.c
$(OUTPUT_DIR)/ML16.exe: EXTRA = ml16-native.c
$(OUTPUT_DIR)/Scope.exe: EXTRA = -ccopt -O3
$(OUTPUT_DIR)/Test128.exe: EXTRA = -fnouint128 -static-header FStar -fsopt --normalize_pure_terms_for_extraction
$(OUTPUT_DIR)/HigherOrder.exe: EXTRA = -warn-error +9
$(OUTPUT_DIR)/C89.exe: EXTRA = -ccopts -Wno-long-long,-Wno-format,-pedantic -fc89
$(OUTPUT_DIR)/Debug.exe: EXTRA = -d c-calls
$(OUTPUT_DIR)/Server.exe: EXTRA = -add-include '"kremstr.h"' main-Server.c
$(OUTPUT_DIR)/StringLit.exe: EXTRA = ../kremlib/kremstr.c -add-include '"kremstr.h"'
$(OUTPUT_DIR)/Failwith.exe: EXTRA = -add-include '"kremstr.h"'
$(OUTPUT_DIR)/TailCalls.exe: EXTRA = -add-include '"kremstr.h"' -ftail-calls
$(OUTPUT_DIR)/FunctionalEncoding.exe: EXTRA = -add-include '"kremstr.h"'
$(OUTPUT_DIR)/Crypto_Symmetric_Chacha20.exe: EXTRA+=$(CRYPTO_OPTS) main-Chacha.c
$(OUTPUT_DIR)/HelloSystem.exe: EXTRA = -add-include '"system.h"' \
	hello-system/system.c -I hello-system -no-prefix SystemNative \
	-drop SystemNative -add-include '<netdb.h>'
$(OUTPUT_DIR)/TestKremBytes.exe: EXTRA = -add-include '"krembytes.h"' -add-include \
	'"kremstr.h"' -drop FStar.Bytes ../kremlib/kremstr.c
$(OUTPUT_DIR)/TestAlloca.exe: EXTRA = -falloca
$(OUTPUT_DIR)/EtaStruct.exe: EXTRA = -fnostruct-passing

# Some custom targets

SED=$(shell which gsed >/dev/null 2>&1 && echo gsed || echo sed)
count-uu: $(OUTPUT_DIR)/Uu.exe
	[ `grep uu___ $(OUTPUT_DIR)/Uu.out/Uu.c | \
	  $(SED) 's/.*\(uu____\([0-9]\+\)\).*/\1/g' \
	  | uniq | wc -l | bc` = 1 ]

# External C tests that leverage other projects.
.PHONY: hacl-test
hacl-test:
	$(MAKE) -C $(HACL_HOME)/code/curve25519 extract-c
	$(MAKE) -C $(HACL_HOME)/secure_api -f $(HACL_HOME)/secure_api/Makefile.extract krml-test

# A target for WASM compilation. All WASM targets get the -wasm flag;
# some specific targets may override NEGATIVE for negative tests.
$(OUTPUT_DIR)/%.wasm: EXTRA += -wasm
$(OUTPUT_DIR)/%.wasm: $(OUTPUT_DIR)/FStar_UInt128.krml $(OUTPUT_DIR)/WasmSupport.krml | $(KRML_BIN)
	$(KRML) $(EXTRA) -tmpdir $(subst .wasm,.out,$@) $(JSFILES) \
	  -no-prefix $(notdir $*) $(filter-out $(OUTPUT_DIR)/prims.krml,$^)

%.wasm-test: $(OUTPUT_DIR)/$$(notdir $$(subst .,_,$$*)).wasm
	cd $(OUTPUT_DIR)/$*.out && \
	  if ! $(NEGATIVE); then $(shell which d8) main.js && echo "\033[01;32m✔\033[00m [WASM-TEST,$*]" || echo "\033[01;31m✘\033[00m [WASM-TEST,$*]"; \
	  else ! $(shell which d8) main.js && echo "\033[01;32m✔\033[00m [WASM-TEST,$*]" || echo "\033[01;31m✘\033[00m [WASM-TEST,$*]"; fi

# Customizing some WASM targets.
$(CRYPTO)/Crypto.Symmetric.Chacha20.wasm: JSFILES=main-Chacha.js
$(CRYPTO)/Crypto.Symmetric.Chacha20.wasm: EXTRA+=$(CRYPTO_OPTS) -drop FStar
WasmTrap.wasm-test: NEGATIVE = true

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

# Monolithic rule for extracting with a single .krml file; to be removed once
# HACL* produces separate krml files.
$$($(1))/$$(subst .krml,.wasm,$$($(1)_TEST)): $$($(1))/$$($(1)_TEST)
	$(KRML) -wasm -drop $$(HACL_DROP) $$($(1)_ARGS) -tmpdir $$(subst .wasm,.out,$$@) \
	  -no-prefix $$(subst .krml,,$$($(1)_TEST)) $$<

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

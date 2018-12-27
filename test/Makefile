RECENT_GCC	= $(shell [ "$$(gcc -dumpversion | cut -c -1)" -ge 5 ] && echo yes)
CRYPTO		= $(FSTAR_HOME)/examples/low-level/crypto
CRYPTO_OPTS	= -I $(CRYPTO) -I $(CRYPTO)/real
TEST_OPTS	= -warn-error @4
KRML_BIN	= ../_build/src/Kremlin.native
KRML		= $(KRML_BIN) $(KOPTS) $(TEST_OPTS)
FILES		= \
  TestKremBytes.test Hoisting.test Flat.test Renaming.test Vla.test Inline.test \
  Fill.test \
  Private.test ML16.test Abbrev.test Tuples.test \
  DataTypesSimple.test DataTypes.test Parameterized.test \
  Scope.test Attributes.test Unsound.test Substitute.test \
  InlineTest.test Ghost1.test Loops.test Structs.test \
  TotalLoops.test \
  Recursive.test RecursivePoly.test Structs2.test StringLit.test \
  FunctionalEncoding.test FunPtr.test Test128.test \
  CheckedInt.test Polymorphic.test GcTypes.test BadMatch.test C89.test \
  PatternAny.test hello-system/HelloSystem.test Server.test \
  ExitCode.test DataTypesMut.test ParamAbbrev.test Null.test Failwith.test \
  CustomEq.test Uu.test WildCard.test UnusedParameter.test EqB.test MutRec.test \
  MallocFree.test TestAlloca.test OptimizedOption.test PushPop.test EtaStruct.test \
  Verbatim.test Const.test $(CRYPTO)/Crypto.Symmetric.Chacha20.test Uu.test \
  LinkedList1.test LinkedList2.test LinkedList3.test LinkedList4.test \
  NoExtract.test InlineNoExtract.test ../book/RingBuffer.test \
  ../book/Introduction.test TopLevelArray.test NoShadow.test Library.test \
  AbstractStruct.test HigherOrder.test HigherOrder2.test HigherOrder3.test \
  UBuffer.test HigherOrder4.fst HigherOrder5.fst TailCalls.test DataTypesEq.test
ifeq ($(RECENT_GCC),"yes")
  FILES 	+= Debug.test
endif
CUSTOM		= count-uu
WASM_FILES	= \
  WasmTrap.wasm-test Wasm1.wasm-test Wasm2.wasm-test Wasm3.wasm-test \
  Wasm4.wasm-test Wasm5.wasm-test Wasm6.wasm-test
NEGATIVE	= false
# Chacha20: need to pass StackInline information properly
BROKEN		= \
  HigherOrder6.fst RecordTypingLimitation.fst

WEB_DIR		?= web
CACHE_DIR	= .cache
OUTPUT_DIR	= .output
HINTS_DIR	= .hints
FSTAR		= fstar.exe --cache_checked_modules --use_two_phase_tc true \
  --cache_dir $(CACHE_DIR) --odir $(OUTPUT_DIR) \
  --include hello-system --include ../kremlib/compat \
  --include ../kremlib --include ../runtime \
  --include $(CRYPTO) --include ../book --use_hints --record_hints --hint_info

# This just needs F* + KreMLin
all: $(FILES) $(CUSTOM)

# Needs node
wasm: $(WASM_FILES)

# Needs a checkout of HACL*
external: hacl-test hacl-algs

# All of the above
everything: all wasm external

.PRECIOUS: %.krml

# Use F*'s dependency mechanism and fill out the missing rules.

.depend: $(subst .wasm-test,.fst,$(WASM_FILES)) $(subst .test,.fst,$(FILES)) $(BROKEN) | Makefile
	$(FSTAR) --dep full $^ ../runtime/WasmSupport.fst --extract Kremlin > .depend

-include .depend

$(HINTS_DIR):
	mkdir -p $@

$(CACHE_DIR)/%.checked: | .depend $(HINTS_DIR)
	$(FSTAR) --hint_file $(HINTS_DIR)/$*.hints $< && \
	touch $@

$(OUTPUT_DIR)/%.krml: | .depend
	$(FSTAR) --codegen Kremlin \
	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	  $(notdir $(subst .checked,,$<))

$(OUTPUT_DIR)/%.exe: $(OUTPUT_DIR)/FStar_UInt128.krml | $(KRML_BIN)
	$(KRML) $(EXTRA) -tmpdir $(subst .exe,.out,$@) -no-prefix $(notdir $*) \
	  -o $@ $^

.SECONDEXPANSION:
%.test: $(OUTPUT_DIR)/$$(notdir $$(subst .,_,$$*)).exe
	@$^ && echo "\033[01;32m✔\033[00m [TEST,$*]" || (echo "\033[01;31m✘\033[00m [TEST,$*]" && false)

ifeq ($(OS),Windows_NT)
  HELLOSYSTEM_LDOPTS = -ldopts -lws2_32
endif

# Various flags to be passed to some targets...
$(OUTPUT_DIR)/Structs2.exe: EXTRA = -wasm -d force-c wasm-stubs.c
$(OUTPUT_DIR)/ML16.exe: EXTRA = ml16-native.c
$(OUTPUT_DIR)/Scope.exe: EXTRA = -ccopt -O3
# libkremlib.a being passed last, the symbols are already resolved for uint128
# against the extracted implementation... slightly hackish
$(OUTPUT_DIR)/Test128.exe: EXTRA = -extract-uints -static-header FStar -ccopt -DKRML_VERIFIED_UINT128
$(OUTPUT_DIR)/HigherOrder.exe: EXTRA = -warn-error +9
$(OUTPUT_DIR)/C89.exe: EXTRA = -ccopts -Wno-long-long,-Wno-format,-pedantic -fc89
$(OUTPUT_DIR)/Debug.exe: EXTRA = -d c-calls
$(OUTPUT_DIR)/Server.exe: EXTRA = main-Server.c helpers-Server.c
$(OUTPUT_DIR)/StringLit.exe: EXTRA = -add-include '"kremlin/internal/compat.h"'
$(OUTPUT_DIR)/TailCalls.exe: EXTRA = -add-include '"kremlin/internal/compat.h"' -ftail-calls
$(OUTPUT_DIR)/FunctionalEncoding.exe: EXTRA = -add-include '"kremlin/internal/compat.h"'
$(OUTPUT_DIR)/Crypto_Symmetric_Chacha20.exe: EXTRA+=$(CRYPTO_OPTS) main-Chacha.c
$(OUTPUT_DIR)/HelloSystem.exe: EXTRA = -add-include '"system.h"' \
	hello-system/system.c -I hello-system -no-prefix SystemNative \
	-drop SystemNative $(HELLOSYSTEM_LDOPTS)
$(OUTPUT_DIR)/TestKremBytes.exe: EXTRA = -add-include '"kremlin/internal/compat.h"'
$(OUTPUT_DIR)/TestAlloca.exe: EXTRA = -falloca
$(OUTPUT_DIR)/EtaStruct.exe: EXTRA = -fnostruct-passing
$(OUTPUT_DIR)/TotalLoops.exe: EXTRA = -add-include '"kremlin/internal/compat.h"'
$(OUTPUT_DIR)/CheckedInt.exe: EXTRA = -add-include '"kremlin/internal/compat.h"'
$(OUTPUT_DIR)/CustomEq.exe: EXTRA = -add-include '"kremlin/internal/compat.h"'
$(OUTPUT_DIR)/DataTypes.exe: EXTRA = -fnoshort-enums
$(OUTPUT_DIR)/NoShadow.exe: EXTRA = -ccopt -Wshadow -fno-shadow
$(OUTPUT_DIR)/Library.exe: EXTRA = -library MemCpyModel memcpymodel_impl.c

# Some custom targets

SED=$(shell which gsed >/dev/null 2>&1 && echo gsed || echo sed)
count-uu: $(OUTPUT_DIR)/Uu.exe
	[ `grep uu___ $(OUTPUT_DIR)/Uu.out/Uu.c | \
	  $(SED) 's/.*\(uu____\([0-9]\+\)\).*/\1/g' \
	  | uniq | wc -l` = 1 ]

# External C tests that leverage other projects.
.PHONY: hacl-test
hacl-test:
	$(MAKE) -C $(HACL_HOME)/code/old/curve25519 extract-c
	$(MAKE) -C $(HACL_HOME)/code/old/api extract-c
	IMPL_CHOICE=runtime_switch $(MAKE) -C $(HACL_HOME)/secure_api -f $(HACL_HOME)/secure_api/Makefile.extract krml-test

# A pseudo-target for WASM compilation that does not match any specific file.
# All WASM targets get the -wasm flag; some specific targets may override
# NEGATIVE for negative tests.
$(OUTPUT_DIR)/%.wasm: $(OUTPUT_DIR)/FStar_UInt128.krml $(OUTPUT_DIR)/WasmSupport.krml | $(KRML_BIN)
	$(KRML) -wasm $(EXTRA) -tmpdir $@ $(JSFILES) -no-prefix $* $^

%.wasm-test: $(OUTPUT_DIR)/%.wasm
	cd $^ && \
	  if ! $(NEGATIVE); then node main.js && echo "\033[01;32m✔\033[00m [WASM-TEST,$*]" || (echo "\033[01;31m✘\033[00m [WASM-TEST,$*]" && false); \
	  else ! node main.js && echo "\033[01;32m✔\033[00m [WASM-TEST,$*]" || (echo "\033[01;31m✘\033[00m [WASM-TEST,$*]" && false); fi

# Customizing some WASM targets.
$(CRYPTO)/Crypto.Symmetric.Chacha20.wasm: JSFILES=main-Chacha.js
$(CRYPTO)/Crypto.Symmetric.Chacha20.wasm: EXTRA+=$(CRYPTO_OPTS) -drop FStar
WasmTrap.wasm-test: NEGATIVE = true

# External WASM targets: recycle the HACL* Makefile!
HACL_DROP=Prims,Hacl.UInt8,Hacl.UInt16,Hacl.UInt32,Hacl.UInt64,Hacl.UInt128,Hacl.Compat.Endianness,Hacl.Endianness,Hacl.Cast,Hacl.Spe.*,Hacl.Spec.*,Spec.*,Seq.*
HACL_ALGS=CHACHA SALSA CURVE POLY ED # HMAC

# Arguments to the meta-rule
CHACHA=$(HACL_HOME)/code/old/salsa-family
CHACHA_DIR=chacha-c
CHACHA_TEST=Hacl.Test.Chacha20.krml
CHACHA_ARGS=-bundle 'Hacl_Chacha20=Hacl.Impl.*,Chacha20,Hacl.Lib.*'

SALSA=$(HACL_HOME)/code/old/salsa-family
SALSA_DIR=salsa-c
SALSA_TEST=Hacl.Test.Salsa20.krml
SALSA_ARGS=-bundle 'Hacl_Salsa20=Salsa20,Hacl.Impl.*,Hacl.Lib.*'

CURVE=$(HACL_HOME)/code/old/curve25519
CURVE_DIR=x25519-c
CURVE_TEST=Hacl.Test.X25519.krml
CURVE_ARGS=-bundle 'Hacl_Curve25519=Hacl.Bignum,Hacl.Bignum.*,Hacl.EC,Hacl.EC.*'

POLY=$(HACL_HOME)/code/old/poly1305
POLY_DIR=poly-c
POLY_TEST=Hacl.Test.Poly1305_64.krml
POLY_ARGS=-bundle 'Hacl_Poly1305_64=Hacl.Bignum.*,Hacl.Impl.*,Hacl.Standalone.*,Poly1305_64' \
  -drop AEAD_Poly1305_64

ED=$(HACL_HOME)/code/old/ed25519
ED_DIR=ed25519-c
ED_TEST=Hacl.Test.Ed25519.krml
ED_ARGS=-bundle 'Hacl_Ed25519=Ed25519,Hacl.EC,Hacl.EC.*,Hacl.Impl.*,Hacl.Lib.*,Hacl.Bignum.*,Hacl.Bignum25519,Hacl.Bignum,Hacl.Spec.*,Hacl.SHA2_512,Hacl.Hash.*' \

HMAC=$(HACL_HOME)/code/old/hmac
HMAC_DIR=hmac-sha256-c
HMAC_TEST=Hacl.Test.HMAC.SHA2_256.krml
HMAC_ARGS=-bundle 'Hacl_HMAC_SHA2_256=Hacl.Hash.Lib.Create,Hacl.Hash.Lib.LoadStore,Hacl.Hash.SHA2_256,Hacl.HMAC.SHA2_256,HMAC_SHA2_256,Hacl.Impl.*'

# A template that uses the global namespace as an associative array. Note:
# equals sign is not Make 3.81-compatible (last GPLv2 version on OSX).
define HACL_template
.PHONY: $$($(1))/$$($(1)_TEST)
$$($(1))/$$($(1)_TEST):
	KREMLIN_ARGS=-wasm $$(MAKE) -C $$($(1)) $$($(1)_DIR)/out.krml
	[ -e $$(subst .krml,.out,$$@) ] || ln -sf $$($(1))/$$($(1)_DIR) $$(subst .krml,.out,$$@)
	cp $$(subst .krml,.out,$$@)/out.krml $$@

# Monolithic rule for extracting with a single .krml file; to be removed once
# HACL* produces separate krml files. This overrides the %.wasm rule above.
$$(OUTPUT_DIR)/$$(subst .krml,.wasm,$$($(1)_TEST)): $$($(1))/$$($(1)_TEST) | $(KRML_BIN)
	$(KRML) -wasm -drop $$(HACL_DROP) $$($(1)_ARGS) -tmpdir $$@ \
	  -no-prefix $$(subst .krml,,$$($(1)_TEST)) $$<

hacl-algs: $$(subst .krml,.wasm-test,$$($(1)_TEST))

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
	rm -rf $(WEB_DIR) .output

distclean: clean clean-hacl
	rm -rf .cache
	$(MAKE) -C $(HACL_HOME)/secure_api clean

# Generation of a mini-website
web-head:
	mkdir -p $(WEB_DIR)
	echo "<h1>WHACL* -- Web HACL*</h1><ul>" > $(WEB_DIR)/index.html

web-body: web-head

$(WEB_DIR): web-body

%.fst-in:
	@echo --include ../kremlib

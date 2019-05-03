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
  Recursive.test RecursivePoly.test Structs2.test \
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
  UBuffer.test HigherOrder4.fst HigherOrder5.fst TailCalls.test DataTypesEq.test \
  ProperErasure.test EmptyStruct.test IfDef.test StringLit.test IfThenElse.test
ifeq ($(RECENT_GCC),"yes")
  FILES 	+= Debug.test
endif
CUSTOM		= count-uu
WASM_FILES	= \
  WasmTrap.wasm-test Wasm1.wasm-test Wasm2.wasm-test Wasm3.wasm-test \
  Wasm4.wasm-test Wasm5.wasm-test Wasm6.wasm-test Wasm7.wasm-test \
  Wasm8.wasm-test Wasm9.wasm-test Wasm10.wasm-test
NEGATIVE	= false
# Chacha20: need to pass StackInline information properly
BROKEN		= \
  HigherOrder6.fst RecordTypingLimitation.fst ForwardDecl.fst

WEB_DIR		?= web
CACHE_DIR	= .cache
OUTPUT_DIR	= .output
HINTS_DIR	= .hints
FSTAR		= fstar.exe --cache_checked_modules --use_two_phase_tc true \
  --cache_dir $(CACHE_DIR) --odir $(OUTPUT_DIR) \
  --include hello-system --include ../kremlib/compat \
  --include ../kremlib --include ../runtime \
  --include $(CRYPTO) --include ../book --use_hints --record_hints \
  --already_cached 'Prims FStar C TestLib Spec.Loops -C.Compat -C.Nullity'

# This just needs F* + KreMLin
all: $(FILES) $(CUSTOM)

# Needs node
wasm: $(WASM_FILES)

# All of the above
everything: all wasm

.PRECIOUS: %.krml

# Use F*'s dependency mechanism and fill out the missing rules.

ifndef MAKE_RESTARTS
.depend: .FORCE
	$(FSTAR) --dep full $(subst .wasm-test,.fst,$(WASM_FILES)) $(subst .test,.fst,$(FILES)) \
	  $(BROKEN) ../runtime/WasmSupport.fst --extract Kremlin > $@

.PHONY: .FORCE
.FORCE:
endif

include .depend

$(HINTS_DIR):
	mkdir -p $@

$(CACHE_DIR)/%.checked: | .depend $(HINTS_DIR)
	$(FSTAR) --hint_file $(HINTS_DIR)/$*.hints $< && \
	touch $@

$(OUTPUT_DIR)/%.krml: | .depend
	$(FSTAR) --codegen Kremlin \
	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	  $(notdir $(subst .checked,,$<))

.PRECIOUS: $(OUTPUT_DIR)/%.exe
$(OUTPUT_DIR)/%.exe: $(ALL_KRML_FILES) $(KRML_BIN)
	$(KRML) $(EXTRA) -tmpdir $(subst .exe,.out,$@) -no-prefix $(notdir $*) \
	  -o $@ $(filter %.krml,$^) -bundle $(subst _,.,$*)=WindowsHack,\*

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
$(OUTPUT_DIR)/Library.exe: EXTRA = -bundle MemCpyModel= -library MemCpyModel memcpymodel_impl.c
$(OUTPUT_DIR)/IfDef.exe: EXTRA = -ccopt -DX

# Some custom targets

SED=$(shell which gsed >/dev/null 2>&1 && echo gsed || echo sed)
count-uu: $(OUTPUT_DIR)/Uu.exe
	[ `grep uu___ $(OUTPUT_DIR)/Uu.out/Uu.c | \
	  $(SED) 's/.*\(uu____\([0-9]\+\)\).*/\1/g' \
	  | uniq | wc -l` = 1 ]

# A pseudo-target for WASM compilation that does not match any specific file.
# All WASM targets get the -wasm flag; some specific targets may override
# NEGATIVE for negative tests.
.PRECIOUS: $(OUTPUT_DIR)/%.wasm
$(OUTPUT_DIR)/%.wasm: $(ALL_KRML_FILES) $(KRML_BIN)
	$(KRML) -minimal -bundle WasmSupport= -bundle 'FStar.*' -bundle Prims \
	  -bundle C -bundle C.Endianness -bundle C.Nullity -bundle C.String \
	  -bundle TestLib \
	  -bundle $(subst _,.,$*)=WindowsHack,\* \
	  -wasm $(EXTRA) -tmpdir $@ $(JSFILES) -no-prefix $* $(filter %.krml,$^)

%.wasm-test: $(OUTPUT_DIR)/%.wasm
	cd $^ && \
	  if ! $(NEGATIVE); then node main.js && echo "\033[01;32m✔\033[00m [WASM-TEST,$*]" || (echo "\033[01;31m✘\033[00m [WASM-TEST,$*]" && false); \
	  else ! node main.js && echo "\033[01;32m✔\033[00m [WASM-TEST,$*]" || (echo "\033[01;31m✘\033[00m [WASM-TEST,$*]" && false); fi

# Customizing some WASM targets.
$(CRYPTO)/Crypto.Symmetric.Chacha20.wasm: JSFILES=main-Chacha.js
$(CRYPTO)/Crypto.Symmetric.Chacha20.wasm: EXTRA+=$(CRYPTO_OPTS) -drop FStar
WasmTrap.wasm-test: NEGATIVE = true

clean:
	rm -rf $(WEB_DIR) .output

distclean: clean
	rm -rf .cache

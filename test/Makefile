RECENT_GCC	= $(shell [ "$$(gcc -dumpversion | cut -c -1)" -ge 5 ] && echo yes)
CRYPTO		= $(FSTAR_HOME)/examples/low-level/crypto
CRYPTO_OPTS	= -I $(CRYPTO) -I $(CRYPTO)/real
TEST_OPTS	= -warn-error @4 -verbose -skip-makefiles
KRML_BIN	= ../_build/src/Kremlin.native
KRML		= $(KRML_BIN) $(KOPTS) $(TEST_OPTS)

BROKEN		= \
  HigherOrder6.fst ForwardDecl.fst BlitNull.fst \
  Ctypes1.fst Ctypes2.fst Ctypes3.fst Ctypes4.fst

# Lowlevel is not really broken, but its test shouldn't be run since it's a
# special file and doesn't have a main.
FILES		= \
  $(patsubst %.fst,%.test,$(filter-out Unused_A.fst StaticHeaderAPI.fst StaticHeaderLib.fst NameCollisionHelper.fst ML16Externals.fst MemCpyModel.fst Lowlevel.fst $(BROKEN),$(wildcard *.fst))) \
  $(CRYPTO)/Crypto.Symmetric.Chacha20.test \
  $(patsubst %.fst,%.test,$(wildcard ../book/*.fst ../book/notfslit/*.fst))

ifneq ($(RECENT_GCC),"yes")
  FILES 	:= $(filter-out Debug.test,$(FILES))
endif

CUSTOM		= count-uu check-unused
WASM_FILES	= \
  WasmTrap.wasm-test Wasm1.wasm-test Wasm2.wasm-test Wasm3.wasm-test \
  Wasm4.wasm-test Wasm5.wasm-test Wasm6.wasm-test Wasm7.wasm-test \
  Wasm8.wasm-test Wasm9.wasm-test Wasm10.wasm-test Crypto.Symmetric.Chacha20.wasm-test
NEGATIVE	= false

WEB_DIR		?= web
CACHE_DIR	= .cache
OUTPUT_DIR	= .output
HINTS_DIR	= .hints

ifdef FSTAR_HOME
  # Assume there is a F* source tree
  FSTAR_EXE=$(FSTAR_HOME)/bin/fstar.exe
else
  # Assume F* in the PATH
  FSTAR_EXE=fstar.exe
endif

FSTAR		= $(FSTAR_EXE) --cache_checked_modules --use_two_phase_tc true \
  --cache_dir $(CACHE_DIR) --odir $(OUTPUT_DIR) \
  --include hello-system --include ../kremlib/compat --include ../kremlib/obj \
  --include ../kremlib --include ../runtime \
  --include $(CRYPTO) --include ../book --include ../book/notfslit --use_hints --record_hints \
  --already_cached 'Prims FStar C TestLib Spec.Loops -C.Compat -C.Nullity LowStar WasmSupport' \
  --trivial_pre_for_unannotated_effectful_fns false \
  --cmi

# This just needs F* + KreMLin
all: $(FILES) $(CUSTOM) ctypes-test sepcomp-test

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
	$(FSTAR) $(OTHERFLAGS) --hint_file $(HINTS_DIR)/$*.hints $< && \
	touch $@

$(OUTPUT_DIR)/%.krml: | .depend
	$(FSTAR) $(OTHERFLAGS) --codegen Kremlin \
	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	  $(notdir $(subst .checked,,$<))

$(OUTPUT_DIR)/Ctypes2.exe: $(ALL_KRML_FILES) $(KRML_BIN)
	$(KRML) $(EXTRA) -tmpdir $(subst .exe,.out,$@) \
	  -o $@ $(filter %.krml,$^) \
        -skip-compilation $(filter %.krml,$^) \

.PRECIOUS: $(OUTPUT_DIR)/%.exe
$(OUTPUT_DIR)/%.exe: $(filter-out %/prims.krml,$(ALL_KRML_FILES)) $(KRML_BIN)
	$(KRML) $(EXTRA) -tmpdir $(subst .exe,.out,$@) -no-prefix $(notdir $*) \
	  -o $@ $(filter %.krml,$^) -bundle $(subst _,.,$*)=WindowsHack,\*

.SECONDEXPANSION:
%.test: $(OUTPUT_DIR)/$$(notdir $$(subst .,_,$$*)).exe
	@(if $(NEGATIVE); then ! $^; else $^; fi) && echo "\033[01;32m✔\033[00m [TEST,$*]" || (echo "\033[01;31m✘\033[00m [TEST,$*]" && false)

ifeq ($(OS),Windows_NT)
  HELLOSYSTEM_LDOPTS = -ldopts -lws2_32
endif

# Various flags to be passed to some targets...
$(OUTPUT_DIR)/Structs2.exe: EXTRA = -wasm -d force-c wasm-stubs.c
$(OUTPUT_DIR)/ML16.exe: EXTRA = ml16-native.c
$(OUTPUT_DIR)/Scope.exe: EXTRA = -ccopt -O3
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
$(OUTPUT_DIR)/Ctypes2.exe: EXTRA = -ctypes 'Ctypes2,Ctypes4' \
  -bundle 'Ctypes3+Ctypes4=[rename=Lowlevel]' \
  -bundle 'Ctypes2=' \
  -bundle 'Ctypes1=' \
  -bundle '*,WindowsHack[rename=Leftovers]' \
  -no-prefix 'Ctypes4' -skip-compilation
$(OUTPUT_DIR)/Failwith.exe: EXTRA = -ccopts -Wno-deprecated-declarations,-Wno-infinite-recursion
$(OUTPUT_DIR)/VariableMerge.exe: EXTRA = -fmerge aggressive
$(OUTPUT_DIR)/NameCollision.exe: EXTRA = -no-prefix NameCollisionHelper
$(OUTPUT_DIR)/Intro.exe $(OUTPUT_DIR)/MemCpy.exe: EXTRA = -rst-snippets
$(OUTPUT_DIR)/StaticHeader.exe: EXTRA = -static-header StaticHeaderLib -bundle StaticHeaderAPI=StaticHeaderLib -warn-error @7@8
$(OUTPUT_DIR)/Unused_B.exe: EXTRA=-bundle Unused_A

Failure.test: NEGATIVE=true

# Some custom targets

SED=$(shell which gsed >/dev/null 2>&1 && echo gsed || echo sed)
count-uu: $(OUTPUT_DIR)/Uu.exe
	[ `grep uu___ $(OUTPUT_DIR)/Uu.out/Uu.c | \
	  $(SED) 's/.*\(uu____\([0-9]\+\)\).*/\1/g' \
	  | uniq | wc -l` = 1 ]

check-unused: $(OUTPUT_DIR)/Unused_B.exe
	egrep -q 'gets_eliminated.*foobar\)' $(OUTPUT_DIR)/Unused_B.out/Unused_A.c

check-no-constructor: $(OUTPUT_DIR)/NoConstructor.exe
	! grep -q define $(OUTPUT_DIR)/NoConstructor.out/NoConstructor.c

# Custom ctypes target

LOWLEVEL_DIR=$(OUTPUT_DIR)/Ctypes2.out

$(LOWLEVEL_DIR)/%: ctypes/%
	mkdir -p $(dir $@)
	cp $< $@

ctypes-test: $(LOWLEVEL_DIR)/Client.native
	cd $(LOWLEVEL_DIR)/_build && export LD_LIBRARY_PATH=. && \
	  ./Client.native && ./Client.byte

sepcomp-test:
	+$(MAKE) -C sepcomp
.PHONY: sepcomp-test

CTYPES_HAND_WRITTEN_FILES=myocamlbuild.ml Client.ml _tags

.PHONY: $(LOWLEVEL_DIR)/Client.native
$(LOWLEVEL_DIR)/Client.native: $(OUTPUT_DIR)/Ctypes2.exe $(addprefix $(LOWLEVEL_DIR)/,$(CTYPES_HAND_WRITTEN_FILES))
	cd $(dir $@) && \
	  CTYPES_LIB_DIR=$(shell ocamlfind query ctypes) ocamlbuild -use-ocamlfind $(notdir $@) Client.byte


# A pseudo-target for WASM compilation that does not match any specific file.
# All WASM targets get the -wasm flag; some specific targets may override
# NEGATIVE for negative tests.
.PRECIOUS: $(OUTPUT_DIR)/%.wasm
$(OUTPUT_DIR)/%.wasm: $(filter-out %/prims.krml,$(ALL_KRML_FILES)) $(KRML_BIN)
	$(KRML) -minimal -bundle WasmSupport= -bundle 'FStar.*' -bundle Prims \
	  -bundle C -bundle C.Endianness -bundle C.Nullity -bundle C.String \
	  -bundle TestLib \
	  -bundle $(subst _,.,$*)=WindowsHack,\* \
	  -wasm $(EXTRA) -tmpdir $@ $(JSFILES) -no-prefix $* $(filter %.krml,$^)
	[ x$(JSFILES) != x ] && cp $(JSFILES) $@ || true

%.wasm-test: $(OUTPUT_DIR)/%.wasm
	cd $^ && \
	  if ! $(NEGATIVE); then node main.js && echo "\033[01;32m✔\033[00m [WASM-TEST,$*]" || (echo "\033[01;31m✘\033[00m [WASM-TEST,$*]" && false); \
	  else ! node main.js && echo "\033[01;32m✔\033[00m [WASM-TEST,$*]" || (echo "\033[01;31m✘\033[00m [WASM-TEST,$*]" && false); fi

# Customizing some WASM targets.
%/Crypto.Symmetric.Chacha20.wasm: JSFILES=./main-Chacha.js
%/Crypto.Symmetric.Chacha20.wasm: EXTRA+=$(CRYPTO_OPTS) -drop FStar
WasmTrap.wasm-test: NEGATIVE = true

clean:
	rm -rf $(WEB_DIR) .output

distclean: clean
	rm -rf .cache

# This file is only to verify KaRaMeL as a library, i.e. to place all
# *.checked files in this directory instead of a cache. This
# is to allow users to directly pick from these .checked files instead
# of rebuilding them. This Makefile assumes that everything else from
# the F* standard library is already built (and fails otherwise)

all: verify-all compile-all

.PHONY: all verify-all compile-all


################################################################################
# Verification & extraction                                                    #
################################################################################

ifdef FSTAR_HOME
  # Assume there is a F* source tree
  FSTAR_EXE=$(FSTAR_HOME)/bin/fstar.exe
else
  # Assume F* in the PATH
  FSTAR_EXE=fstar.exe
endif

EXTRACT_DIR = .extract

GENERIC_DIR = dist/generic
UINT128_DIR = dist/uint128
MINI_DIR = dist/minimal

#332 is turning abstract keyword usage into a fatal error
FSTAR_OPTIONS += --record_hints --use_hints --odir $(EXTRACT_DIR) \
  --warn_error @332
  # --use_extracted_interfaces

INCLUDE_PATHS = ../runtime

# Passing RESOURCEMONITOR=1 to this Makefile will create .runlim files
# throughout the tree with resource information. The $(RUNLIM) variable
# can also be defined directly if needed. The results can then be
# tallied with the res_summary.sh script.
ifneq ($(RESOURCEMONITOR),)
  RUNLIM = runlim -p -o $@.runlim
endif

FSTAR = $(RUNLIM) $(FSTAR_EXE) $(FSTAR_OPTIONS) --cache_checked_modules --cache_dir obj \
  --hint_dir hints \
  $(addprefix --include , $(INCLUDE_PATHS)) --cmi \
  --already_cached 'Prims FStar -FStar.Krml.Endianness LowStar -LowStar.Lib'

# Note: not compatible with the OPAM layout until fstar can be queried for the
# location of ulib.
ROOTS = $(wildcard *.fst) $(wildcard *.fsti) $(wildcard ../runtime/*.fst) \
  FStar.UInt128.fst FStar.Date.fsti \
    FStar.HyperStack.IO.fst FStar.IO.fst FStar.Int.Cast.Full.fst \
    FStar.Bytes.fsti FStar.Dyn.fsti LowStar.Printf.fst LowStar.Endianness.fst

.PHONY: clean clean-c
clean: clean-c
	rm -rf *.checked *.source .depend

SHELL:=$(shell which bash)

clean-c:
	rm -rf dist out extract-all */*.o

FSTAR_EXTRACT:=*
FSTAR_EXTRACT+=-Prims # No prims, F* won't extract it anyway
FSTAR_EXTRACT+=-FStar.Tactics -FStar.Reflection # No tactics modules
FSTAR_EXTRACT+=-FStar.Stubs # This namespace is for interfaces into the compiler, nothing we want to extract here

ifndef NODEPEND
ifndef MAKE_RESTARTS
.depend: .FORCE obj
	$(FSTAR) $(OTHERFLAGS) --extract '$(FSTAR_EXTRACT)' --dep full $(ROOTS) --output_deps_to $@

.PHONY: .FORCE
.FORCE:
endif
endif

include .depend

obj:
	mkdir $@

%.checked: | obj
	$(FSTAR) $(OTHERFLAGS) $< && \
	touch $@

verify-all: $(ALL_CHECKED_FILES)

$(EXTRACT_DIR)/%.krml: | .depend
	$(FSTAR) $(OTHERFLAGS) --codegen krml \
	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	  $(notdir $(subst .checked,,$<)) && \
	touch -c $@

# We don't extract LowStar.Lib as everything is generic data structures that
# need to be specialized based on their usage from client code.
KRML_ARGS += -fparentheses -fcurly-braces -fno-shadow -header copyright-header.txt \
  -minimal -skip-compilation -extract-uints \
  -bundle 'LowStar.Lib.\*'

MACHINE_INTS = \
  -bundle FStar.UInt64+FStar.UInt32+FStar.UInt16+FStar.UInt8=[rename=FStar_UInt_8_16_32_64] \
  -library FStar.UInt128 \
  -bundle FStar.UInt128= \
  -static-header FStar.UInt128 \
  -hand-written FStar.UInt128

$(MINI_DIR):
	mkdir -p $@

$(GENERIC_DIR):
	mkdir -p $@

# Everything in the universe
$(GENERIC_DIR)/Makefile.include: $(ALL_KRML_FILES) | $(GENERIC_DIR) $(wildcard c/*.c) $(wildcard c/*.h) ../_build/default/src/Karamel.exe
	KRML_HOME=$(shell pwd)/.. \
	../krml $(KRML_ARGS) -tmpdir $(GENERIC_DIR) \
	  -warn-error +9+11 \
	  $(MACHINE_INTS) \
	  $(addprefix -add-include ,'<inttypes.h>' '"krmllib.h"' '"krml/internal/compat.h"' '"krml/internal/target.h"') \
	  -bundle LowStar.Endianness= \
	  -bundle FStar.Endianness,FStar.Range \
	  -library C,C.Endianness,C.Failure,C.Loops,FStar.BitVector,FStar.Bytes,FStar.Char,FStar.Int,FStar.Krml.Endianness,FStar.Math.Lib,FStar.ModifiesGen,FStar.Monotonic.Heap,FStar.Monotonic.HyperStack,FStar.Mul,FStar.Pervasives,FStar.Pervasives.Native,FStar.ST,FStar.UInt,FStar.UInt63,LowStar.Printf \
	  -bundle FStar.BV \
	  $(filter-out fstar_uint128_msvc.c,$(notdir $(wildcard c/*.c))) \
	  -o libkrmllib.a \
	  $^
	cp c/*.c c/*.h $(dir $@)

# Minimalistic build (just machine integers and endianness)
$(MINI_DIR)/Makefile.include: $(ALL_KRML_FILES) | $(MINI_DIR) $(wildcard c/fstar_uint128*.h) ../_build/default/src/Karamel.exe
	mkdir -p $(dir $@)
	KRML_HOME=$(shell pwd)/.. \
	../krml $(KRML_ARGS) -tmpdir $(MINI_DIR) \
	  $(MACHINE_INTS) \
	  $(addprefix -add-include , \
	    '<inttypes.h>' '<stdbool.h>' \
	    '"krml/internal/compat.h"' \
	    '"krml/lowstar_endianness.h"' \
	    '"krml/internal/types.h"' \
	    '"krml/internal/target.h"') \
	  -bundle LowStar.Endianness= \
	  -bundle '*,WindowsWorkaroundSigh' \
	  fstar_uint128.c \
	  -o libkrmllib.a \
	  $^
	cp c/fstar_uint128_struct_endianness.h c/fstar_uint128_gcc64.h c/fstar_uint128_msvc.h $(dir $@)

# Extracted (and verified) uint128s; copied into generic and minimal. Note that
# FStar.UInt64 shares the same bundle name, meaning that
# FStar_UInt128_Verified.h can be dropped in any of the two krmllibs above.
$(UINT128_DIR)/Makefile.include: $(ALL_KRML_FILES) | $(GENERIC_DIR) $(MINI_DIR) ../_build/default/src/Karamel.exe
	KRML_HOME=$(shell pwd)/.. \
	../krml $(KRML_ARGS) -tmpdir $(UINT128_DIR) \
	  $(addprefix -add-include ,'<inttypes.h>' '<stdbool.h>' '"krml/internal/types.h"' '"krml/internal/target.h"') \
	  -bundle FStar.UInt64[rename=FStar_UInt_8_16_32_64] \
	  -bundle FStar.UInt128=[rename=FStar_UInt128_Verified] \
	  -fc89 \
	  -bundle '*,WindowsWorkaroundSigh' \
	  -static-header FStar.UInt128,FStar.UInt64 \
	  -ccopt -DKRML_VERIFIED_UINT128 \
	  -o libkrmllib.a \
	  $^
	cp $(dir $@)/FStar_UInt128_Verified.h $(GENERIC_DIR)/
	cp $(dir $@)/FStar_UInt128_Verified.h $(MINI_DIR)/

################################################################################
# Compilation, only works after the stage above has run and C files exist      #
################################################################################

CFLAGS += -O3
export CFLAGS

compile-all: compile-dist-generic $(MINI_DIR)/Makefile.include $(UINT128_DIR)/Makefile.include

.PHONY: compile-dist-%
compile-dist-%: dist/%/Makefile.include
	KRML_HOME=$(shell pwd)/.. \
	$(MAKE) -C dist/$* -f Makefile.basic

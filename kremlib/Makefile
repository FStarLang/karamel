# This file is only to verify KreMLib as a library, i.e. to place all
# *.checked files in this directory instead of a cache. This
# is to allow users to directly pick from these .checked files instead
# of rebuilding them. This Makefile assumes that everything else from
# the F* standard library is already built (and fails otherwise)

all: verify-all extract-all
	COMPILE=1 $(MAKE) compile-all

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

OUTPUT_DIR = extracted
UINT128_DIR = dist/uint128
MINI_DIR = dist/minimal

$(OUTPUT_DIR):
	mkdir -p $@

FSTAR_OPTIONS += --record_hints --use_hints --use_two_phase_tc true --odir $(OUTPUT_DIR) \
  # --use_extracted_interfaces

FSTAR = $(FSTAR_EXE) $(FSTAR_OPTIONS) --cache_checked_modules \
  $(addprefix --include , $(INCLUDE_PATHS))

# Note: not compatible with the OPAM layout until fstar can be queried for the
# location of ulib.
ROOTS = $(wildcard *.fst) $(wildcard *.fsti) \
  $(addprefix $(FSTAR_HOME)/ulib/,FStar.UInt128.fst FStar.Date.fsti \
    FStar.HyperStack.IO.fst FStar.IO.fst FStar.Int.Cast.Full.fst \
    FStar.Bytes.fsti FStar.Dyn.fsti)

.PHONY: clean clean-c
clean: clean-c
	rm -rf *.checked *.source .depend

SHELL=/bin/bash

clean-c:
	rm -rf {$(OUTPUT_DIR),$(UINT128_DIR)}/{Makefile.include,*.{c,h}} out extract-all */*.o

.depend: Makefile | $(OUTPUT_DIR)
	$(FSTAR) $(OTHERFLAGS) --dep full $(ROOTS) > $@

include .depend

ALL_CHECKED_FILES	= $(addsuffix .checked, $(ALL_FST_FILES))
KREMLIB_FILES		= $(wildcard *.fst) $(wildcard *.fsti)
KREMLIB_CHECKED_FILES	= $(addsuffix .checked, $(KREMLIB_FILES))
OTHER_CHECKED_FILES	= $(filter-out $(KREMLIB_CHECKED_FILES), $(ALL_CHECKED_FILES))

$(KREMLIB_CHECKED_FILES): %.checked: | .depend
	$(FSTAR) $(FSTAR_OPTIONS) $(OTHERFLAGS) $< && \
	touch $@

$(OTHER_CHECKED_FILES): %.checked:
	@echo $@ is out of date, please run make -C '$$'\(FSTAR_HOME\)/ulib before; false

verify-all: $(ALL_CHECKED_FILES)

$(OUTPUT_DIR)/%.krml:  | .depend
	$(FSTAR) $(OTHERFLAGS) --codegen Kremlin \
	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	  $(notdir $(subst .checked,,$<)) && \
	touch $@

extract-all: $(OUTPUT_DIR)/Makefile.include $(UINT128_DIR)/Makefile.include \
  $(MINI_DIR)/Makefile.include

KREMLIN_ARGS += -fparentheses -fcurly-braces -fno-shadow

# Default build
$(OUTPUT_DIR)/Makefile.include: $(ALL_KRML_FILES) | .depend ../_build/src/Kremlin.native
	../krml $(KREMLIN_ARGS) -minimal -tmpdir $(OUTPUT_DIR) -warn-error +9+11 -skip-compilation -extract-uints \
	  $(addprefix -add-include ,'<inttypes.h>' '"kremlib.h"' '"kremlin/internal/compat.h"') \
	  $^
	find $(OUTPUT_DIR) -name '*.c' -and -not -name 'FStar_UInt*.c' -exec rm {} \;

# UInt128-only build
$(UINT128_DIR)/Makefile.include: $(ALL_KRML_FILES) | .depend ../_build/src/Kremlin.native
	# Workaround windows issue: kremlin doesn't recursively create
	# directories.
	mkdir -p $(dir $@)
	../krml $(KREMLIN_ARGS) -minimal -tmpdir $(dir $@) -skip-compilation -extract-uints \
	  $(addprefix -add-include ,'<inttypes.h>' '<stdbool.h>' '"kremlin/internal/types.h"') \
	  -bundle FStar.UInt128=* $^

# Minimalistic build
$(MINI_DIR)/Makefile.include: $(ALL_KRML_FILES) | $(UINT128_DIR)/Makefile.include .depend ../_build/src/Kremlin.native
	# Workaround windows issue: kremlin doesn't recursively create
	# directories.
	mkdir -p $(dir $@)
	../krml $(KREMLIN_ARGS) -minimal -tmpdir $(dir $@) -skip-compilation -extract-uints \
	  $(addprefix -add-include , \
	    '<inttypes.h>' '<stdbool.h>' '"kremlin/internal/compat.h"' \
	    '"kremlin/internal/types.h"') \
	  -bundle FStar.UInt64+FStar.UInt32+FStar.UInt16+FStar.UInt8=* $^
	cp c/fstar_uint128.c $(dir $@)
	cp $(UINT128_DIR)/FStar_UInt128.h $(dir $@)

################################################################################
# Compilation, only works after the stage above has run and C files exist      #
################################################################################

ifdef COMPILE

include $(OUTPUT_DIR)/Makefile.include

SOURCES = $(filter-out c/fstar_uint128_msvc.c,$(wildcard c/*.c)) \
  $(addprefix extracted/,FStar_UInt8.c FStar_UInt16.c FStar_UInt32.c FStar_UInt64.c)
OBJS = $(patsubst %.c,%.o,$(SOURCES))

%.d: %.c
	@set -e; rm -f $@; \
	  $(CC) -MM $(CFLAGS) $< > $@.$$$$; \
	  sed 's,\($(notdir $*)\)\.o[ :]*,$(dir $@)\1.o $@ : ,g' < $@.$$$$ > $@; \
	  rm -f $@.$$$$


include $(patsubst %.c,%.d,$(SOURCES))

CFLAGS += -I extracted -I ../include -Wall -Wextra -Werror -g -std=c11 -D_DEFAULT_SOURCE -D_BSD_SOURCE
ifeq ($(OS),Windows_NT)
CFLAGS += -D__USE_MINGW_ANSI_STDIO
else
CFLAGS += -fPIC
endif

$(UINT128_DIR)/FStar_UInt128.o: CFLAGS += -DKRML_VERIFIED_UINT128
$(MINI_DIR)/%.o: CFLAGS += -I$(MINI_DIR)

compile-all: out/libkremlib.a $(UINT128_DIR)/FStar_UInt128.o \
  $(MINI_DIR)/FStar_UInt64_FStar_UInt32_FStar_UInt16_FStar_UInt8.o \
  $(MINI_DIR)/fstar_uint128.o

out/libkremlib.a: $(OBJS) | extract-all
	mkdir -p $(dir $@)
	ar cr $@ $^

endif

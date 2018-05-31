# This file is only to verify KreMLib as a library, i.e. to place all
# *.checked files in this directory instead of a cache. This
# is to allow users to directly pick from these .checked files instead
# of rebuilding them. This Makefile assumes that everything else from
# the F* standard library is already built (and fails otherwise)

all: verify-all extract-all
	$(MAKE) compile-all

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

$(OUTPUT_DIR):
	mkdir -p $@

FSTAR_OPTIONS += --use_hints --use_two_phase_tc true --odir $(OUTPUT_DIR) \
  # --use_extracted_interfaces

FSTAR = $(FSTAR_EXE) $(FSTAR_OPTIONS) --cache_checked_modules \
  $(addprefix --include , $(INCLUDE_PATHS))

# Note: not compatible with the OPAM layout until fstar can be queried for the
# location of ulib.
ROOTS = $(wildcard *.fst) $(wildcard *.fsti) \
  $(addprefix $(FSTAR_HOME)/ulib/,FStar.UInt128.fst FStar.Date.fsti)

.PHONY: clean
clean:
	rm -rf *.checked *.source .depend

.PHONY: .depend
.depend: $(ROOTS) Makefile | $(OUTPUT_DIR)
	$(FSTAR) $(OTHERFLAGS) --dep full $(ROOTS) > $@

include .depend

ALL_CHECKED_FILES=$(addsuffix .checked, $(ALL_FST_FILES))

KREMLIB_CHECKED_FILES=$(addsuffix .checked, $(KREMLIB_FILES))

OTHER_CHECKED_FILES=$(filter-out $(KREMLIB_CHECKED_FILES), $(ALL_CHECKED_FILES))

$(KREMLIB_CHECKED_FILES): %.checked: | .depend
	$(MY_FSTAR) $(FSTAR_OPTIONS) $(OTHERFLAGS) $<
	touch $@

$(OTHER_CHECKED_FILES): %.checked:
	test -f $@

verify-all: $(ALL_CHECKED_FILES)

$(OUTPUT_DIR)/%.krml:  | .depend
	$(FSTAR) --codegen Kremlin \
	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	  $(notdir $(subst .checked,,$<)) && \
	touch $@

extract-all: $(ALL_KRML_FILES)
	krml -minimal -tmpdir $(OUTPUT_DIR) -warn-error +9 -skip-compilation -fnouint128 \
	  $(addprefix -add-include ,'<inttypes.h>' '"kremlib.h"' '"kremlin/internal/compat.h"') \
	  $^
	find $(OUTPUT_DIR) -name '*.c' -and -not -name 'FStar_UInt128.c' -exec rm {} \;
	touch $@

################################################################################
# Compilation, only works after the stage above has run and C files exist      #
################################################################################

ALL_C_FILES = $(wildcard c/*.c)
ALL_OBJ_FILES = $(patsubst %.c,%.o,$(ALL_C_FILES))

CFLAGS += -I extracted -I ../include

compile-all: kremlib.a

kremlib.a: $(ALL_OBJ_FILES)
	ar cr $@ $^

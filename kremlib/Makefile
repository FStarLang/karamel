# This file is only to verify KreMLib as a library, i.e. to place all
# *.checked files in this directory instead of a cache. This
# is to allow users to directly pick from these .checked files instead
# of rebuilding them. This Makefile assumes that everything else from
# the F* standard library is already built (and fails otherwise)

all: verify-all

ifdef FSTAR_HOME
  # Assume there is a F* source tree
  FSTAR_EXE=$(FSTAR_HOME)/bin/fstar.exe
else
  # Assume F* in the PATH
  FSTAR_EXE=fstar.exe
endif

FSTAR_OPTIONS += --use_hints --use_two_phase_tc true # --use_extracted_interfaces

MY_FSTAR=$(FSTAR_EXE) --cache_checked_modules $(addprefix --include , $(INCLUDE_PATHS))

KREMLIB_FILES=$(wildcard *.fst) $(wildcard *.fsti)

clean:
	rm -rf *.checked *.source .depend

.depend: $(KREMLIB_FILES) Makefile
	$(MY_FSTAR) $(FSTAR_OPTIONS) $(OTHERFLAGS) --dep full $(KREMLIB_FILES) > $@

include .depend

ALL_CHECKED_FILES=$(addsuffix .checked, $(ALL_FST_FILES))

KREMLIB_CHECKED_FILES=$(addsuffix .checked, $(KREMLIB_FILES))

OTHER_CHECKED_FILES=$(filter-out $(KREMLIB_CHECKED_FILES), $(ALL_CHECKED_FILES))

verify-all: $(ALL_CHECKED_FILES)

$(KREMLIB_CHECKED_FILES): %.checked:
	$(MY_FSTAR) $(FSTAR_OPTIONS) $(OTHERFLAGS) $<
	touch $@

$(OTHER_CHECKED_FILES): %.checked:
	test -f $@
	$(MY_FSTAR) $(FSTAR_OPTIONS) $(OTHERFLAGS) --warn_error '@241@247' $<

.PHONY: all verify-all clean

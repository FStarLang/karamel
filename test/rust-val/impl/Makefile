RECENT_GCC	= $(shell [ "$$(gcc -dumpversion | cut -c -1)" -ge 5 ] && echo yes)

ifeq (3.81,$(MAKE_VERSION))
  $(error You seem to be using the OSX antiquated Make version. Hint: brew \
    install make, then invoke gmake instead of make)
endif

FSTAR_EXE ?= fstar.exe

TEST_OPTS	= -warn-error @4 -verbose -skip-makefiles
KRML_BIN	= ../../../_build/default/src/Karamel.exe
KRML		= $(KRML_BIN) -fstar $(FSTAR_EXE) $(KOPTS) $(TEST_OPTS)
CACHE_DIR	= .cache
FSTAR		= $(FSTAR_EXE) --cache_checked_modules \
  --cache_dir $(CACHE_DIR) \
  --include ../../../krmllib/compat --include ../../../krmllib/obj \
  --include ../../../krmllib --include ../../../runtime \
  --include .. \
  --ext optimize_let_vc \
  --already_cached 'Prims FStar C TestLib Spec.Loops -C.Compat -C.Nullity LowStar WasmSupport' \
  --trivial_pre_for_unannotated_effectful_fns false \
  --cmi --warn_error -274
SED=$(shell which gsed >/dev/null 2>&1 && echo gsed || echo sed)

all: aux.rust-test

FSTAR_FILES=$(wildcard *.fst *.fsti)

.PRECIOUS: %.krml

# Use F*'s dependency mechanism and fill out the missing rules.

ifndef MAKE_RESTARTS
ifndef NODEPEND
.depend: .FORCE
	$(FSTAR) --dep full $(FSTAR_FILES) --extract 'krml:*,-Prims' --output_deps_to $@

.PHONY: .FORCE
.FORCE:
endif
endif

include .depend

$(CACHE_DIR)/%.checked: | .depend
	$(FSTAR) $(OTHERFLAGS) $< && \
	touch $@

%.krml: | .depend
	$(FSTAR) $(OTHERFLAGS) --codegen krml \
	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	  $(notdir $(subst .checked,,$<))

########
# Rust #
########

.PRECIOUS: %.rs
%.rs: $(ALL_KRML_FILES) $(KRML_BIN)
	$(KRML) -minimal -bundle AuxA+AuxB=\*[rename=Aux,rename-prefix] \
	  -backend rust $(EXTRA) -tmpdir $(dir $@) $(filter %.krml,$^)

%.rust-test: %.rs
	rustc --crate-type rlib $< -o $*.rlib

# This makefile is mostly taken from F*'s mk/test.mk.
# We use it to check that krml works on the Pulse files in this repo and
# produces exactly the expected C output.

# Don't delete intermediates.
.SECONDARY:
# If a rule fails, delete target as it could be corrupted
.DELETE_ON_ERROR:

# Resolve a command to an absolute path.
# Bare names (no /) are looked up in PATH; paths are resolved with abspath.
resolve = $(if $(findstring /,$1),$(abspath $1),$(shell command -v $1))

.DEFAULT_GOAL := all

MAKEFLAGS += --no-builtin-rules
Q?=@
SIL?=--silent
RAMON=
ifneq ($(V),)
	Q=
	SIL=
else
	MAKEFLAGS += -s
endif

define msg =
@printf "   %-14s  %s\n" $(1) $(2)
endef
define bold_msg =
printf -- "  %-15s  %s\n" $(1) $(2)
endef

# Set a default FSTAR_EXE for most clients.
FSTAR_EXE ?= fstar.exe
FSTAR_EXE := $(call resolve,$(FSTAR_EXE))
export FSTAR_EXE

# Make sure F* has Pulse in it...
_ := $(shell $(FSTAR_EXE) --version)
ifneq ($(.SHELLSTATUS),0)
_: $(error "Cannot run F*, aborting (FSTAR_EXE = $(FSTAR_EXE))")
endif
_ := $(shell $(FSTAR_EXE) --list_plugins | grep -q Pulse)
ifneq ($(.SHELLSTATUS),0)
_: $(error "F* ($(FSTAR_EXE)) does not have the Pulse plugin, cannot run these tests.")
endif

FSTAR_ARGS += --odir $(OUTPUT_DIR)
FSTAR_ARGS += --cache_dir $(CACHE_DIR)
FSTAR_ARGS += --already_cached Prims,FStar,Pulse
FSTAR_ARGS += --warn_error -321 # This warning is really useless.
FSTAR_ARGS += $(OTHERFLAGS)

# Set ADMIT=1 to admit queries
FSTAR_ARGS += $(if $(ADMIT),--admit_smt_queries true)

KRML_EXE ?= ../../krml
_ := $(shell $(KRML_EXE) -help)
ifneq ($(.SHELLSTATUS),0)
_: $(error "Cannot run krml, aborting (KRML_EXE = $(KRML_EXE))")
endif

# Almost everything goes into the OUTPUT_DIR, except for .checked files
# which go in the CACHE_DIR. The .depend goes in the current directory.
# Extracted files, executables, touch files (.diff), outputs (.out), etc,
# all go in the OUTPUT_DIR. This makes cleaning up pretty easy.
OUTPUT_DIR ?= _output
CACHE_DIR ?= _cache

FSTAR = $(FSTAR_EXE) $(SIL) $(FSTAR_ARGS)

ifneq ($(MAKECMDGOALS),clean)
ifeq ($(NODEPEND),) # Set NODEPEND=1 to not dependency analysis
FSTAR_FILES ?= $(wildcard *.fst) $(wildcard *.fsti)
FSTAR_FILES := $(strip $(FSTAR_FILES))

ifneq ($(FSTAR_FILES),) # It anyway only runs if fst/fsti files are found in the cwd
.depend: $(FSTAR_FILES)
	$(call msg, "DEPEND", $(CURDIR))
	$(FSTAR) --dep full $(FSTAR_FILES) -o $@
depend: .depend
include .depend
endif

endif
endif

# These will be in the cache directory due to the .depend
%.fst.checked:
	$(call msg, "CHECK", $(basename $(notdir $@)))
	$(FSTAR) -c $< -o $@
	touch -c $@

%.fsti.checked:
	$(call msg, "CHECK", $(basename $(notdir $@)))
	$(FSTAR) -c $< -o $@
	touch -c $@

$(OUTPUT_DIR)/$(subst .,_,%).krml:
	$(call msg, "EXTRACT", $(basename $(notdir $@)))
	$(FSTAR) $< --codegen krml --extract_module $(subst .fst.checked,,$(notdir $<))

$(OUTPUT_DIR)/%.c: $(OUTPUT_DIR)/%.krml $(OUTPUT_DIR)/Pulse_Lib_Pervasives.krml
	$(call msg, "KRML", $(basename $(notdir $@)))
	$(KRML_EXE) $(KRML_FLAGS) -skip-compilation -header=krmlheader -bundle $*=* -skip-linking $+ -tmpdir $(OUTPUT_DIR)

### Checking expected output for any kind of file
$(OUTPUT_DIR)/%.diff: $(OUTPUT_DIR)/% %.expected
	$(call msg, "DIFF", $<)
	bash ./diff.sh $^
	touch $@

$(OUTPUT_DIR)/%.accept: $(OUTPUT_DIR)/%
	$(call msg, "ACCEPT", $<)
	cp $< ./$*.expected
	touch $(OUTPUT_DIR)/$*.diff # touch so subsequent test skips

# Subrules for descending into subdirectories (coallesce with a define?)

%.__depend: # Make sure to sequeantlize the .depend for each subdir, to avoid duplication and races
	$(MAKE) -C $* depend

%.__all:
	$(MAKE) -C $* all

%.__verify:
	$(MAKE) -C $* verify

%.__clean:
	$(MAKE) -C $* clean

%.__accept:
	$(MAKE) -C $* accept

SUBDIRS_ALL += $(SUBDIRS)
all: $(addsuffix .__all, $(SUBDIRS_ALL))
# __verify: check all files here and in subdirectories (SUBDIRS / SUBDIRS_VERIFY)
# Implied by 'all' for each directory, but we cannot write 'all: verify' or we
# will get duplicate invocations for all/verify on a same subdir, and they overlap.
SUBDIRS_VERIFY += $(SUBDIRS)
__verify: $(ALL_CHECKED_FILES)
verify: $(addsuffix .__verify, $(SUBDIRS_VERIFY))
verify: __verify
ifeq ($(NOVERIFY),)
all: __verify
endif

# clean
SUBDIRS_CLEAN += $(SUBDIRS)
clean: $(addsuffix .__clean, $(SUBDIRS_CLEAN))
__clean:
	rm -rf $(OUTPUT_DIR) $(CACHE_DIR) .depend
clean: __clean

__extract: $(patsubst %.fst,$(OUTPUT_DIR)/%.ml,$(EXTRACT))
extract: __extract
all: __extract

__diff: $(patsubst %.expected,$(OUTPUT_DIR)/%.diff,$(wildcard *.expected))
diff: __diff
ifeq ($(NODIFF),)
ifeq ($(ACCEPT),1)
all: __accept
else
all: __diff
endif
endif

accept: $(addsuffix .__accept,$(SUBDIRS))
__accept: $(patsubst %.expected,$(OUTPUT_DIR)/%.accept,$(wildcard *.expected))
accept: __accept

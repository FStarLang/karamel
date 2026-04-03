include ../../Makefile.common

# Standalone test suite for -finitialize-locals.
# Tests run with each of c23, c99, c89 modes and verify correct execution.

ifeq (3.81,$(MAKE_VERSION))
  $(error You seem to be using the OSX antiquated Make version. Hint: brew \
    install make, then invoke gmake instead of make)
endif

FSTAR_EXE ?= fstar.exe
KRML_BIN = ../../_build/default/src/Karamel.exe
TEST_OPTS = -warn-error @4 -skip-makefiles

CACHE_DIR = .cache
OUTPUT_DIR = .output

FSTAR = $(FSTAR_EXE) \
  --cache_dir $(CACHE_DIR) --odir $(OUTPUT_DIR) \
  --include ../../krmllib/compat --include ../../krmllib/obj \
  --include ../../krmllib --include ../../runtime \
  --already_cached 'Prims FStar C TestLib LowStar WasmSupport' \
  --trivial_pre_for_unannotated_effectful_fns false \
  --cmi --warn_error -274

KRML = $(KRML_BIN) -fstar $(FSTAR_EXE) $(TEST_OPTS)

comma := ,

FILES = InitLocals

all: $(addsuffix .test-c23,$(FILES)) \
     $(addsuffix .test-c99,$(FILES)) \
     $(addsuffix .test-c89,$(FILES)) \
     check-c23 check-c99 check-c89

.PRECIOUS: %.krml

# Dependency analysis
ifndef MAKE_RESTARTS
ifndef NODEPEND
.depend: .FORCE
	@mkdir -p $(CACHE_DIR) $(OUTPUT_DIR)
	$(call run-with-log, \
	  $(FSTAR) --dep full $(addsuffix .fst,$(FILES)) \
	    --extract 'krml:*' -o $@ \
	  ,[DEPEND],\
	  .depend)

.PHONY: .FORCE
.FORCE:
endif
endif

include .depend

$(CACHE_DIR)/%.checked: | .depend
	@mkdir -p $(CACHE_DIR)
	$(call run-with-log,$(FSTAR) $(OTHERFLAGS) -c $< -o $@ && touch $@,[VERIFY] $*,$(CACHE_DIR)/$*)

$(OUTPUT_DIR)/%.krml: | .depend
	@mkdir -p $(OUTPUT_DIR)
	$(call run-with-log, \
	  $(FSTAR) $(OTHERFLAGS) --codegen krml \
	    --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	    -o $@ \
	    $< \
	 ,[EXTRACT] $*,\
	  $(OUTPUT_DIR)/$*)

#################
# Build targets #
#################

# C23 mode: = {}
.PRECIOUS: $(OUTPUT_DIR)/%.c23.exe
$(OUTPUT_DIR)/%.c23.exe: $(ALL_KRML_FILES) $(KRML_BIN) | .depend
	@mkdir -p $(OUTPUT_DIR)
	$(call run-with-log, \
	  $(KRML) -finitialize-locals c23 -tmpdir $(subst .exe,.out,$@) -no-prefix $(notdir $*) \
	    -o $@ $(filter %.krml,$^) -bundle $(subst _,.,$*)=*$(comma)WindowsHack \
	,[KRML-c23] $*,$(OUTPUT_DIR)/$*.c23)

# C99 mode: designated initializers
.PRECIOUS: $(OUTPUT_DIR)/%.c99.exe
$(OUTPUT_DIR)/%.c99.exe: $(ALL_KRML_FILES) $(KRML_BIN) | .depend
	@mkdir -p $(OUTPUT_DIR)
	$(call run-with-log, \
	  $(KRML) -finitialize-locals c99 -tmpdir $(subst .exe,.out,$@) -no-prefix $(notdir $*) \
	    -o $@ $(filter %.krml,$^) -bundle $(subst _,.,$*)=*$(comma)WindowsHack \
	,[KRML-c99] $*,$(OUTPUT_DIR)/$*.c99)

# C89 mode: positional initializers
.PRECIOUS: $(OUTPUT_DIR)/%.c89.exe
$(OUTPUT_DIR)/%.c89.exe: $(ALL_KRML_FILES) $(KRML_BIN) | .depend
	@mkdir -p $(OUTPUT_DIR)
	$(call run-with-log, \
	  $(KRML) -finitialize-locals c89 -tmpdir $(subst .exe,.out,$@) -no-prefix $(notdir $*) \
	    -o $@ $(filter %.krml,$^) -bundle $(subst _,.,$*)=*$(comma)WindowsHack \
	,[KRML-c89] $*,$(OUTPUT_DIR)/$*.c89)

################
# Test targets #
################

.SECONDEXPANSION:
%.test-c23: $(OUTPUT_DIR)/$$(notdir $$(subst .,_,$$*)).c23.exe
	@($^ && echo -e "\033[01;32m✔\033[00m [TEST-C23,$*]") || (echo -e "\033[01;31m✘\033[00m [TEST-C23,$*]" && false)

%.test-c99: $(OUTPUT_DIR)/$$(notdir $$(subst .,_,$$*)).c99.exe
	@($^ && echo -e "\033[01;32m✔\033[00m [TEST-C99,$*]") || (echo -e "\033[01;31m✘\033[00m [TEST-C99,$*]" && false)

%.test-c89: $(OUTPUT_DIR)/$$(notdir $$(subst .,_,$$*)).c89.exe
	@($^ && echo -e "\033[01;32m✔\033[00m [TEST-C89,$*]") || (echo -e "\033[01;31m✘\033[00m [TEST-C89,$*]" && false)

##################
# Custom targets #
##################

# C23: verify C23 initializer syntax (= { }) is used for uninitialized vars
check-c23: $(OUTPUT_DIR)/InitLocals.c23.exe
	@echo -e "\033[01;32m✔\033[00m [CHECK,c23-execution]"

# C99: verify code compiles and runs with c99 initializers
check-c99: $(OUTPUT_DIR)/InitLocals.c99.exe
	@echo -e "\033[01;32m✔\033[00m [CHECK,c99-execution]"

# C89: verify code compiles and runs with c89 initializers
check-c89: $(OUTPUT_DIR)/InitLocals.c89.exe
	@echo -e "\033[01;32m✔\033[00m [CHECK,c89-execution]"

clean:
	rm -rf $(CACHE_DIR) $(OUTPUT_DIR) .depend *.cmd *.output *.err *.time *~

.PHONY: all clean

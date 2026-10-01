include ../../Makefile.common

# Standalone test suite for -fhoist-locals (HoistLocals pass).
# For each test, we compile with and without -fhoist-locals, run both,
# and compare their stdout to ensure identical output.

ifeq (3.81,$(MAKE_VERSION))
  $(error You seem to be using the OSX antiquated Make version. Hint: brew \
    install make, then invoke gmake instead of make)
endif

FSTAR_EXE ?= fstar.exe
KRML_BIN = ../../out/bin/krml
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

# Tests where output must be identical with and without -fhoist-locals
TESTS = HoistInt HoistArray HoistScope HoistVlaNoWarn HoistComment

# Tests that exercise the VLA warning (compiled with -warn-error -29)
WARN_TESTS = HoistVlaWarn

# Tests that verify comment/declaration ordering in the generated C source
ORDER_TESTS = HoistComment

ALL_TESTS = $(TESTS) $(WARN_TESTS)

all: $(addsuffix .compare,$(TESTS)) $(addsuffix .warn-test,$(WARN_TESTS)) \
     $(addsuffix .order-test,$(ORDER_TESTS))

.PRECIOUS: %.krml $(OUTPUT_DIR)/%.krml

# Dependency analysis
ifndef MAKE_RESTARTS
ifndef NODEPEND
.depend: .FORCE
	@mkdir -p $(CACHE_DIR) $(OUTPUT_DIR)
	$(call run-with-log, \
	  $(FSTAR) --dep full $(addsuffix .fst,$(ALL_TESTS)) \
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

# Build WITHOUT -fhoist-locals
.PRECIOUS: $(OUTPUT_DIR)/%.nohoist.exe
$(OUTPUT_DIR)/%.nohoist.exe: $(ALL_KRML_FILES) $(KRML_BIN) | .depend
	@mkdir -p $(OUTPUT_DIR)
	$(call run-with-log, \
	  $(KRML) $(EXTRA) -tmpdir $(subst .exe,.out,$@) -no-prefix $(notdir $*) \
	    -o $@ $(filter %.krml,$^) -bundle $(subst _,.,$*)=*$(comma)WindowsHack \
	,[KRML-nohoist] $*,$(OUTPUT_DIR)/$*.nohoist)

# Build WITH -fhoist-locals
.PRECIOUS: $(OUTPUT_DIR)/%.hoist.exe
$(OUTPUT_DIR)/%.hoist.exe: $(ALL_KRML_FILES) $(KRML_BIN) | .depend
	@mkdir -p $(OUTPUT_DIR)
	$(call run-with-log, \
	  $(KRML) $(EXTRA) -fhoist-locals -tmpdir $(subst .exe,.out,$@) -no-prefix $(notdir $*) \
	    -o $@ $(filter %.krml,$^) -bundle $(subst _,.,$*)=*$(comma)WindowsHack \
	,[KRML-hoist] $*,$(OUTPUT_DIR)/$*.hoist)

# Run both versions and compare output
.SECONDEXPANSION:
%.compare: $(OUTPUT_DIR)/$$(notdir $$(subst .,_,$$*)).nohoist.exe $(OUTPUT_DIR)/$$(notdir $$(subst .,_,$$*)).hoist.exe
	@echo "Running $* without -fhoist-locals..."
	@$(word 1,$^) > $(OUTPUT_DIR)/$*.nohoist.stdout 2>&1
	@echo "Running $* with -fhoist-locals..."
	@$(word 2,$^) > $(OUTPUT_DIR)/$*.hoist.stdout 2>&1
	@if diff -u $(OUTPUT_DIR)/$*.nohoist.stdout $(OUTPUT_DIR)/$*.hoist.stdout > /dev/null 2>&1; then \
	  echo -e "\033[01;32m✔\033[00m [COMPARE,$*] outputs identical"; \
	else \
	  echo -e "\033[01;31m✘\033[00m [COMPARE,$*] outputs differ:"; \
	  diff -u $(OUTPUT_DIR)/$*.nohoist.stdout $(OUTPUT_DIR)/$*.hoist.stdout; \
	  false; \
	fi

# VLA warning tests: compile with -warn-error -29 to make the warning non-fatal,
# then run and compare
$(OUTPUT_DIR)/HoistVlaWarn.nohoist.exe: EXTRA = -warn-error -6
$(OUTPUT_DIR)/HoistVlaWarn.hoist.exe: EXTRA = -warn-error -6-29

%.warn-test: $(OUTPUT_DIR)/$$(notdir $$(subst .,_,$$*)).nohoist.exe $(OUTPUT_DIR)/$$(notdir $$(subst .,_,$$*)).hoist.exe
	@echo "Running $* without -fhoist-locals..."
	@$(word 1,$^) > $(OUTPUT_DIR)/$*.nohoist.stdout 2>&1
	@echo "Running $* with -fhoist-locals..."
	@$(word 2,$^) > $(OUTPUT_DIR)/$*.hoist.stdout 2>&1
	@if diff -u $(OUTPUT_DIR)/$*.nohoist.stdout $(OUTPUT_DIR)/$*.hoist.stdout > /dev/null 2>&1; then \
	  echo -e "\033[01;32m✔\033[00m [WARN-TEST,$*] outputs identical"; \
	else \
	  echo -e "\033[01;31m✘\033[00m [WARN-TEST,$*] outputs differ:"; \
	  diff -u $(OUTPUT_DIR)/$*.nohoist.stdout $(OUTPUT_DIR)/$*.hoist.stdout; \
	  false; \
	fi

# VLA no-warn tests: verify that -fhoist-locals does NOT produce warning 29
$(OUTPUT_DIR)/HoistVlaNoWarn.nohoist.exe: EXTRA = -warn-error -6
$(OUTPUT_DIR)/HoistVlaNoWarn.hoist.exe: EXTRA = -warn-error -6

# Order test: verify that comments and initialisers/assignments appear in the
# same relative order with and without -fhoist-locals.  We normalise the
# generated C by stripping the type prefix from declarations (so that
# "int32_t x = 1;" and "x = 1;" both become "x = 1;") and compare.
%.order-test: $(OUTPUT_DIR)/$$(notdir $$(subst .,_,$$*)).nohoist.exe $(OUTPUT_DIR)/$$(notdir $$(subst .,_,$$*)).hoist.exe
	@echo "Checking comment/init order for $*..."
	@grep -E 'MARKER|int32_t [a-z_][a-z0-9_]* = |^ +[a-z_][a-z0-9_]* = ' \
	  $(subst .exe,.out,$(word 1,$^))/$*.c \
	  | sed 's/int32_t //; s/^ *//' > $(OUTPUT_DIR)/$*.nohoist.order
	@grep -E 'MARKER|int32_t [a-z_][a-z0-9_]* = |^ +[a-z_][a-z0-9_]* = ' \
	  $(subst .exe,.out,$(word 2,$^))/$*.c \
	  | sed 's/int32_t //; s/^ *//' > $(OUTPUT_DIR)/$*.hoist.order
	@if diff -u $(OUTPUT_DIR)/$*.nohoist.order $(OUTPUT_DIR)/$*.hoist.order > /dev/null 2>&1; then \
	  echo -e "\033[01;32m✔\033[00m [ORDER,$*] comment/init order preserved"; \
	else \
	  echo -e "\033[01;31m✘\033[00m [ORDER,$*] comment/init order differs:"; \
	  diff -u $(OUTPUT_DIR)/$*.nohoist.order $(OUTPUT_DIR)/$*.hoist.order; \
	  false; \
	fi

clean:
	rm -rf $(CACHE_DIR) $(OUTPUT_DIR) .depend *.cmd *.output *.err *.time *~

.PHONY: all clean

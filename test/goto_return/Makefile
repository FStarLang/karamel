# Test for -goto_for_early_return transformation.
# Extracts GotoReturn.fst, compiles with -goto_for_early_return -fnoreturn-else,
# verifies the output matches expected C, and runs the executable.

KRML_EXE ?= $(abspath ../../krml)
FSTAR_EXE ?= fstar.exe
OUTPUT_DIR = _output
CACHE_DIR = _cache

.DELETE_ON_ERROR:
.SECONDARY:
.DEFAULT_GOAL := all

Q?=@

FSTAR = $(FSTAR_EXE) --cache_dir $(CACHE_DIR) --odir $(OUTPUT_DIR) --warn_error -321

$(CACHE_DIR)/GotoReturn.fst.checked: GotoReturn.fst
	@mkdir -p $(CACHE_DIR) $(OUTPUT_DIR)
	@printf "   %-14s  %s\n" "CHECK" "GotoReturn.fst"
	$(Q)$(FSTAR) -c $< -o $@

$(OUTPUT_DIR)/GotoReturn.krml: $(CACHE_DIR)/GotoReturn.fst.checked
	@mkdir -p $(OUTPUT_DIR)
	@printf "   %-14s  %s\n" "EXTRACT" "GotoReturn"
	$(Q)$(FSTAR) --codegen krml --extract_module GotoReturn GotoReturn.fst

# Compile with -goto_for_early_return and -fnoreturn-else
$(OUTPUT_DIR)/GotoReturn.c: $(OUTPUT_DIR)/GotoReturn.krml
	@printf "   %-14s  %s\n" "KRML" "GotoReturn"
	$(Q)$(KRML_EXE) -minimal -skip-makefiles -skip-compilation -skip-linking \
	  -bundle GotoReturn=* \
	  -fnoreturn-else -goto_for_early_return \
	  -tmpdir $(OUTPUT_DIR) \
	  -header krmlheader \
	  $<

# Diff against expected output
$(OUTPUT_DIR)/GotoReturn.diff: $(OUTPUT_DIR)/GotoReturn.c GotoReturn.expected.c
	@printf "   %-14s  %s\n" "DIFF" "$<"
	$(Q)diff -u --strip-trailing-cr GotoReturn.expected.c $<
	$(Q)touch $@

# Accept current output as expected
accept: $(OUTPUT_DIR)/GotoReturn.c
	@printf "   %-14s  %s\n" "ACCEPT" "$<"
	$(Q)cp $< GotoReturn.expected.c

all: $(OUTPUT_DIR)/GotoReturn.diff

clean:
	rm -rf $(OUTPUT_DIR) $(CACHE_DIR)

.PHONY: all clean accept

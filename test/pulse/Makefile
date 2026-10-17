include test.mk

# Inline enough so the augmented assignments actually kick in
$(OUTPUT_DIR)/CompoundAssignment.c: KRML_FLAGS += -faggressive-inlining

$(OUTPUT_DIR)/PassByReference.c: KRML_FLAGS += -fnostruct-passing

# Check late inlining with both the default policy and aggressive inlining.
$(OUTPUT_DIR)/LateCleanup.aggressive.c: $(OUTPUT_DIR)/LateCleanup.krml
	$(call msg, "KRML", $(basename $(notdir $@)))
	$(KRML_EXE) $(KRML_FLAGS) -faggressive-inlining -skip-makefiles -skip-compilation -header=../krmlheader -bundle LateCleanup=* -skip-linking $+ -tmpdir $(OUTPUT_DIR)/LateCleanup.aggressive
	cp $(OUTPUT_DIR)/LateCleanup.aggressive/LateCleanup.c $@

include test.mk

# Some tests have extra dependencies.
$(OUTPUT_DIR)/Example_Hashtable.c: $(addprefix $(OUTPUT_DIR)/,\
	FStar_Pervasives.krml \
	FStar_Pervasives_Native.krml \
	Pulse_Lib_Vec.krml \
	Pulse_Lib_HashTable_Type.krml \
	Pulse_Lib_HashTable_Spec.krml \
	Pulse_Lib_HashTable.krml)

$(OUTPUT_DIR)/Example_Slice.c: $(addprefix $(OUTPUT_DIR)/,\
	Pulse_Lib_Slice.krml)

$(OUTPUT_DIR)/Example_Unreachable.c: $(addprefix $(OUTPUT_DIR)/,\
	FStar_Pervasives.krml \
	FStar_Pervasives_Native.krml)

# Inline enough so the augmented assignments actually kick in
$(OUTPUT_DIR)/CompoundAssignment.c: KRML_FLAGS += -faggressive-inlining

$(OUTPUT_DIR)/PassByReference.c: KRML_FLAGS += -fnostruct-passing

# Check late inlining with both the default policy and aggressive inlining.
$(OUTPUT_DIR)/LateCleanup.aggressive.c: $(OUTPUT_DIR)/LateCleanup.krml $(OUTPUT_DIR)/Pulse_Lib_Pervasives.krml
	$(call msg, "KRML", $(basename $(notdir $@)))
	$(KRML_EXE) $(KRML_FLAGS) -faggressive-inlining -skip-makefiles -skip-compilation -header=krmlheader -bundle LateCleanup=* -skip-linking $+ -tmpdir $(OUTPUT_DIR)/LateCleanup.aggressive
	cp $(OUTPUT_DIR)/LateCleanup.aggressive/LateCleanup.c $@

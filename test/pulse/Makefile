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

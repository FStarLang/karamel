INCLUDES = $(KREMLIN_HOME)/kremlib $(DIRS)
FSTAR_INCLUDES = $(addprefix --include ,$(INCLUDES))
OUTPUT_DIR = .extracted

CTYPES = $(shell ocamlfind query ctypes)

FSTAR_NO_FLAGS = $(FSTAR_HOME)/bin/fstar.exe --odir $(OUTPUT_DIR) \
  --cache_checked_modules $(FSTAR_INCLUDES) --cmi \
  --already_cached 'FStar LowStar C'

FSTAR = $(FSTAR_NO_FLAGS) $(OTHERFLAGS)
KRML = $(KREMLIN_HOME)/krml

# F* source files to be extracted
DIRS = .
ROOTS = $(wildcard $(addsuffix /*.fsti,$(DIRS)) $(addsuffix /*.fst,$(DIRS)))

# Use F* to build dependency graph for ROOTS
ifndef MAKE_RESTARTS
.depend: .FORCE
	@$(FSTAR_NO_FLAGS) --dep full $(ROOTS) --extract '* -Prims -LowStar -Lib.Buffer -Hacl -FStar +FStar.Endianness +FStar.Kremlin.Endianness' > $@

.PHONY: .FORCE
.FORCE:
endif

include .depend

ALL_CHECKED_FILES = $(addsuffix .checked,$(ROOTS))

all: Client.exe

%.checked:
	$(FSTAR) $< && \
	touch $@

.PRECIOUS: %.krml

$(OUTPUT_DIR)/%.krml:
	$(FSTAR) --codegen Kremlin \
	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	  $(notdir $(subst .checked,,$<)) && \
	touch $@

KRML_FLAGS= -bundle Prims \
  -bundle LowStar.* \
  -bundle C,C.String,C.Loops,Spec.Loops,C.Endianness,FStar.*[rename=Lib] \
  -minimal \
  -add-include '"kremlin/internal/types.h"' \
  -add-include '"kremlin/internal/target.h"' \
  -add-include '"kremlin/c_endianness.h"' \
  -add-include '<string.h>' \
  -fno-shadow -fcurly-braces

.PHONY: %.bind
%.bind: $(ALL_KRML_FILES)
	mkdir -p bindings
	$(KRML) $(KRML_FLAGS) \
	  -tmpdir bindings -skip-compilation $(filter %.krml,$^) \
	  -ccopt -Wno-unused \
	  -warn-error @4 \
      -ctypes '$*'

.PHONY: Client.exe
Client.exe: Lowlevel.bind
	cc -I ../../include -c -o Lowlevel.o bindings/Lowlevel.c
	ocamlfind ocamlopt -I bindings -linkpkg -package ctypes,ctypes.foreign,ctypes.stubs -cclib Lowlevel.o bindings/Lowlevel_bindings.ml bindings/Gen_stubs.ml -o bindings/Gen_stubs.exe
	./bindings/Gen_stubs.exe
	ocamlopt -I ../../include -I bindings -I $(CTYPES) -c -o Lowlevel_c_stubs.o bindings/Lowlevel_c_stubs.c
	ocamlfind ocamlopt -I bindings -linkpkg -package ctypes,ctypes.foreign -cclib -Wl,-E -cclib Lowlevel.o Lowlevel_c_stubs.o bindings/Lowlevel_bindings.ml bindings/Lowlevel_stubs.ml Client.ml -o Client.exe #
	./Client.exe

clean:
	rm -f *.exe *.cmi *.cmx *.o *.checked*
	rm -rf .extracted
	rm -rf bindings

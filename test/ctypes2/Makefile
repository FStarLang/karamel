# This tests how -ctypes copes with dependencies, bundles and other renamings (-no-prefix).
# The dependencies of the original .fsts are as follows:
#
#             B
#            /|\
#           / | (D -> Lowlevel)
#          /  |/
#         A2 (A -> Lowlevel)
#
# We call krml with
#  -ctypes 'A,A2'
#  -bundle 'A+D=A,D[rename=Lowlevel]'
#  -no-prefix 'A'
# Lowlevel and A2 are the interfaces that Client.ml uses. The expected behaviour is that
# even though we only call -ctypes on A,A2 the bindings for A will be referred to as Lowlevel
# and will include the other type declarations from the bundle (D) and from other
# dependencies (B). Bindings for B need only be generated once, but referred to twice, both
# from Lowlevel and from A2. Finally, bindings for declarations from A need to drop the
# 'a_*' prefix.


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

all: Client.exe

# Use F* to build dependency graph for ROOTS
ifndef MAKE_RESTARTS
.depend: .FORCE
	@$(FSTAR_NO_FLAGS) --dep full $(ROOTS) --extract '* -Prims -LowStar -Lib.Buffer -Hacl -FStar +FStar.Endianness +FStar.Kremlin.Endianness' > $@

.PHONY: .FORCE
.FORCE:
endif

include .depend

ALL_CHECKED_FILES = $(addsuffix .checked,$(ROOTS))

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
  -add-include '"kremlin/lowstar_endianness.h"' \
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

A.bind: $(ALL_KRML_FILES)
	mkdir -p bindings
	$(KRML) $(KRML_FLAGS) \
	  -tmpdir bindings -skip-compilation $(filter %.krml,$^) \
	  -ccopt -Wno-unused \
	  -warn-error @4 \
      -ctypes 'A,A2' \
      -bundle 'A+D=A,D[rename=Lowlevel]' \
      -no-prefix 'A'

.PHONY: Client.exe
Client.exe: A.bind
	$(CC) -I ../../include -c -o B.o bindings/B.c
	ocamlfind ocamlopt -I bindings/lib -linkpkg -package ctypes,ctypes.foreign,ctypes.stubs -cclib B.o bindings/lib/B_bindings.ml bindings/lib_gen/B_gen.ml -o bindings/B_gen.exe
	cd bindings && ./B_gen.exe
	ocamlopt -I ../../include -I bindings -I $(CTYPES) -c -o B_c_stubs.o bindings/lib/B_c_stubs.c

	$(CC) -I ../../include -c -o Lowlevel.o bindings/Lowlevel.c
	ocamlfind ocamlopt -I bindings/lib -linkpkg -package ctypes,ctypes.foreign,ctypes.stubs -cclib Lowlevel.o bindings/lib/B_bindings.ml bindings/lib/B_stubs.ml bindings/lib/Lowlevel_bindings.ml bindings/lib_gen/Lowlevel_gen.ml -o bindings/Lowlevel_gen.exe
	cd bindings && ./Lowlevel_gen.exe
	ocamlopt -I ../../include -I bindings -I $(CTYPES) -c -o Lowlevel_c_stubs.o bindings/lib/Lowlevel_c_stubs.c

	$(CC) -I ../../include -c -o A2.o bindings/A2.c
	ocamlfind ocamlopt -I bindings/lib -linkpkg -package ctypes,ctypes.foreign,ctypes.stubs -cclib A2.o bindings/lib/B_bindings.ml bindings/lib/B_stubs.ml bindings/lib/A2_bindings.ml bindings/lib_gen/A2_gen.ml -o bindings/A2_gen.exe
	cd bindings && ./A2_gen.exe
	ocamlopt -I ../../include -I bindings -I $(CTYPES) -c -o A2_c_stubs.o bindings/lib/A2_c_stubs.c

	ocamlfind ocamlopt -I bindings -I bindings/lib -linkpkg -package ctypes,ctypes.foreign -cclib -Wl,-E -cclib B.o A2.o Lowlevel.o B_c_stubs.o Lowlevel_c_stubs.o A2_c_stubs.o bindings/lib/B_bindings.ml bindings/lib/B_stubs.ml bindings/lib/Lowlevel_bindings.ml bindings/lib/A2_bindings.ml bindings/lib/Lowlevel_stubs.ml bindings/lib/A2_stubs.ml Client.ml -o Client.exe
	./Client.exe

clean:
	rm -f *.exe *.cmi *.cmx *.o *.checked*
	rm -rf .extracted
	rm -rf bindings

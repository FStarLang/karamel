# This Makefile demonstrates how to build krml-generated ctypes bindings. This
# is the same build procdure as the one from hacl-packages for the HACL* OCaml
# bindings.

all: Client.exe Client.bc

# 1. We handle the compilation of C files here (krml not used as a driver)

ALL_O_FILES=Ctypes2.o Lowlevel.o

KARAMEL_INCLUDES	= \
  -I../../../include \
  -I../../../krmllib/dist/minimal/

CFLAGS += $(KARAMEL_INCLUDES) -I. -fPIC

# This could also be dynamic linking, not demonstrated here
libdemo.a: $(ALL_O_FILES)
	ar r $@ $^

# 2. Compilation of OCaml files + compilation of ctypes-produced C files

.PRECIOUS: %.cmx %.cmi %.cmo

OCAMLOPT=ocamlfind opt -package ctypes,ctypes.stubs -linkpkg -I lib -I .
OCAMLDEP=ocamlfind dep -I lib -slash
OCAMLC	=ocamlfind c -g -package ctypes,ctypes.stubs -linkpkg -I lib -I .

CFLAGS += -I "$(shell ocamlfind query ctypes)" -I "$(shell ocamlfind c -where)" 

ALL_OCAML	= $(patsubst lib_gen/%_gen.ml,%,$(wildcard lib_gen/*_gen.ml))
ALL_C_STUBS	= $(patsubst %,lib/%_c_stubs.o,$(ALL_OCAML))

.depend.ocaml:
	$(OCAMLDEP) $(wildcard lib/*.ml) $(wildcard lib_gen/*.ml) > $@

# ctypes.depend is produced by krml
include .depend.ocaml
include ctypes.depend

%.exe:

lib_gen/%_gen.exe:
	$(OCAMLOPT) $(filter-out %.a,$^) -o $@

%.cmx: %.ml
	$(OCAMLOPT) -c $^ -o $@

%.cmo: %.ml
	$(OCAMLC) -c $^ -o $@


.PRECIOUS: lib/%_stubs.ml
lib/%_stubs.ml: lib/%_c_stubs.c

# The generator (whose compilation is described in ctypes.depend) produces ml
# and C stubs, both of which then need to be compiled using their respective
# toolchains before being linked into the final mixed archive (ocamlmklib)
lib/%_stubs.ml lib/%_c_stubs.c: lib_gen/%_gen.exe
	$<

# bindings + stubs
CTYPES_CMX    = $(CTYPES_DEPS)
CTYPES_ML     = $(patsubst %.cmx,%.ml,$(CTYPES_CMX))
CTYPES_CMI    = $(patsubst %.cmx,%.cmi,$(CTYPES_CMX))
CTYPES_CMO    = $(patsubst %.cmx,%.cmo,$(CTYPES_CMX))

# 3. Mixed archive: by combining the krml-generated C files, the krml-generated
# bindings, the bind

democaml.cma: $(CTYPES_CMO) $(ALL_C_STUBS) libdemo.a
	ocamlmklib -o democaml $(CTYPES_CMO) $(ALL_C_STUBS) -L. -ldemo

democaml.cmxa: $(CTYPES_CMX) $(ALL_C_STUBS) libdemo.a
	ocamlmklib -o democaml $(CTYPES_CMX) $(ALL_C_STUBS) -L. -ldemo

# 4. Client links against native or byte archive and voilà

Client.exe: democaml.cmxa Client.ml
	$(OCAMLOPT) $^ -o $@

Client.bc: democaml.cma Client.ml
	$(OCAMLC) $^ -o $@

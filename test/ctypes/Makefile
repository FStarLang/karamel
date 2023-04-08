# This Makefile demonstrates how to build krml-generated ctypes bindings. This
# is the same build procdure as the one from hacl-packages for the HACL* OCaml
# bindings.

all: Client.exe Client.bc

# 1. C build

ALL_O_FILES=Ctypes2.o Lowlevel.o

KARAMEL_INCLUDES	= \
  -I../../../include \
  -I../../../krmllib/dist/minimal/

CFLAGS += $(KARAMEL_INCLUDES) -I.

libdemo.a: $(ALL_O_FILES)
	ar r $@ $^

.PRECIOUS: %.cmx %.cmi %.cmo

OCAMLOPT=ocamlfind opt -package ctypes,ctypes.stubs -linkpkg -I lib -I .
OCAMLDEP=ocamlfind dep -I lib -slash
OCAMLC	=ocamlfind c -g -package ctypes,ctypes.stubs -linkpkg -I lib -I .

CFLAGS += -I "$(shell ocamlfind query ctypes)" -I "$(shell ocamlfind c -where)" 

ALL_OCAML	= $(patsubst lib_gen/%_gen.ml,%,$(wildcard lib_gen/*_gen.ml))
ALL_BINDINGS	= $(patsubst %,lib/%_bindings.cmx,$(ALL_OCAML))
ALL_GENERATORS	= $(patsubst %,lib_gen/%_gen.exe, $(ALL_OCAML))
ALL_ML_STUBS	= $(patsubst %,lib/%_stubs.cmx,$(ALL_OCAML))
ALL_C_STUBS	= $(patsubst %,lib/%_c_stubs.o,$(ALL_OCAML))

.depend.ocaml:
	$(OCAMLDEP) $(wildcard lib/*.ml) $(wildcard lib_gen/*.ml) > $@

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

lib/%_stubs.ml lib/%_c_stubs.c: lib_gen/%_gen.exe
	$<

CTYPES_CMX    = $(CTYPES_DEPS)
CTYPES_ML     = $(patsubst %.cmx,%.ml,$(CTYPES_CMX))
CTYPES_CMI    = $(patsubst %.cmx,%.cmi,$(CTYPES_CMX))
CTYPES_CMO    = $(patsubst %.cmx,%.cmo,$(CTYPES_CMX))

democaml.cma: $(ALL_BINDINGS) $(CTYPES_CMO) $(ALL_C_STUBS) $(CTYPES_CMX) libdemo.a
	ocamlmklib -o democaml $(CTYPES_CMO) $(ALL_C_STUBS) -L. -ldemo

democaml.cmxa: $(ALL_BINDINGS) $(ALL_ML_STUBS) $(ALL_C_STUBS) libdemo.a
	ocamlmklib -o democaml $(CTYPES_CMX) $(ALL_C_STUBS) -L. -ldemo

Client.exe: democaml.cmxa Client.ml
	$(OCAMLOPT) $^ -o $@

Client.bc: democaml.cma Client.ml
	$(OCAMLC) $^ -o $@


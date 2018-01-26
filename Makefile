# make src/Ast.processed.ml
include $(shell ocamlfind query visitors)/Makefile.preprocess

.PHONY: all minimal clean test

OCAMLBUILD=ocamlbuild -I src -I lib -I parser -I kremlib -use-menhir -use-ocamlfind -classic-display \
 -menhir "menhir --infer --explain"
FLAVOR?=native
TARGETS=Kremlin.$(FLAVOR) Tests.$(FLAVOR)
EXTRA_TARGETS=Ast.inferred.mli kremlib/C.cmx kremlib/TestLib.cmx

ifeq (,$(FSTAR_HOME))
  $(error FSTAR_HOME is not defined, cannot build the OCaml version of kremlib)
endif

all: minimal pre
	OCAMLPATH=$(FSTAR_HOME)/bin $(OCAMLBUILD) $(EXTRA_TARGETS)

minimal:
	@# Workaround Windows bug in OCamlbuild
	$(shell [ -f Kremlin.$(FLAVOR) ] && rm Kremlin.$(FLAVOR); [ -f Tests.$(FLAVOR) ] && rm Tests.$(FLAVOR))
	$(OCAMLBUILD) $(TARGETS)
	ln -sf Kremlin.$(FLAVOR) krml

clean:
	rm -rf krml _build Tests.$(FLAVOR) Kremlin.$(FLAVOR)
	make -C test clean

test: all
	./Tests.native
	+make -C test

# External prerequisites
COMPILER := $(FSTAR_HOME)/bin/fstar.exe
FSTARLIB := $(FSTAR_HOME)/bin/fstarlib/fstarlib.cmxa
pre: $(COMPILER) $(FSTARLIB)

$(COMPILER):
	$(error Could not find fstar.exe in $(FSTAR_HOME); aborting)

$(FSTARLIB):
	$(error Could not find fstarlib.cmxa in $(FSTAR_HOME); aborting)

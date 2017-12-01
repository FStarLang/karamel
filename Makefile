# make src/Ast.processed.ml
include $(shell ocamlfind query visitors)/Makefile.preprocess

.PHONY: all clean test

OCAMLBUILD=ocamlbuild -I src -I lib -I parser -use-menhir -use-ocamlfind -classic-display \
 -menhir "menhir --infer --explain"
FLAVOR?=native
TARGETS=Kremlin.$(FLAVOR) Tests.$(FLAVOR) Visitors.inferred.mli

all:
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

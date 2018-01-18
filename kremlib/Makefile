OCAMLOPT=OCAMLPATH=$(FSTAR_HOME)/bin ocamlfind opt -package fstarlib
all: C.cmx TestLib.cmx

%.cmx: %.ml
	$(OCAMLOPT) $< -c -o $@

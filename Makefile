.PHONY: all clean test

ifdef CROSS
  OCAMLLIB=$(abspath $(shell ocamlfind printconf path))
  OCAMLBUILD=ocamlbuild -toolchain windows -I src -I lib -I parser -use-menhir -use-ocamlfind -classic-display \
   -menhir "menhir --infer --explain" \
	  -ocamldep "ocamldep -predicates custom_ppx -ppx '$(OCAMLLIB)/ppx_deriving/ppx_deriving $(OCAMLLIB)/ppx_deriving/ppx_deriving_show.cma $(OCAMLLIB)/ppx_deriving_yojson/ppx_deriving_yojson.cma'" \
	  -ocamlc "ocamlc -predicates custom_ppx -ppx '$(OCAMLLIB)/ppx_deriving/ppx_deriving $(OCAMLLIB)/ppx_deriving/ppx_deriving_show.cma $(OCAMLLIB)/ppx_deriving_yojson/ppx_deriving_yojson.cma'" \
	  -ocamlopt "ocamlopt -predicates custom_ppx -ppx '$(OCAMLLIB)/ppx_deriving/ppx_deriving $(OCAMLLIB)/ppx_deriving/ppx_deriving_show.cma $(OCAMLLIB)/ppx_deriving_yojson/ppx_deriving_yojson.cma'"
else
OCAMLBUILD=ocamlbuild -I src -I lib -I parser -use-menhir -use-ocamlfind -classic-display \
 -menhir "menhir --infer --explain"
endif

FLAVOR?=native
TARGETS=Kremlin.$(FLAVOR) Tests.$(FLAVOR)

minimal: all

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

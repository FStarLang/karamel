# make src/Ast.processed.ml
include $(shell ocamlfind query visitors)/Makefile.preprocess

.PHONY: all minimal clean test

OCAMLBUILD=ocamlbuild -I src -I lib -I parser -I krmllib -use-menhir -use-ocamlfind \
 -menhir "menhir --infer --explain" -quiet
FLAVOR?=native
TARGETS=Karamel.$(FLAVOR)
EXTRA_TARGETS=Ast.inferred.mli krmllib/C.cmx krmllib/TestLib.cmx krmllib/C.cmo krmllib/TestLib.cmo

ifeq ($(OS),Windows_NT)
  OCAMLPATH_SEP=;
else
  OCAMLPATH_SEP=:
endif

ifdef FSTAR_HOME
  OCAMLPATH:=$(OCAMLPATH)$(OCAMLPATH_SEP)$(FSTAR_HOME)/lib
else
  FSTAR_EXE=$(shell which fstar.exe)
  ifneq ($(FSTAR_EXE),)
    FSTAR_HOME=$(dir $(FSTAR_EXE))/..
    OCAMLPATH:=$(OCAMLPATH)$(OCAMLPATH_SEP)$(FSTAR_HOME)/lib
  else
    $(error "fstar.exe not found, please install FStar")
  endif
endif
export FSTAR_HOME
export OCAMLPATH

all: minimal krmllib
	@OCAML_ERROR_STYLE="short" \
	 $(OCAMLBUILD) $(EXTRA_TARGETS)

minimal: src/AutoConfig.ml src/Version.ml
	@# Workaround Windows bug in OCamlbuild
	$(shell [ -f Karamel.$(FLAVOR) ] && rm Karamel.$(FLAVOR))
	@OCAML_ERROR_STYLE="short" $(OCAMLBUILD) $(TARGETS)
	ln -sf Karamel.$(FLAVOR) krml

krmllib: minimal
	$(MAKE) -C krmllib

src/AutoConfig.ml:
	@if [ x"$(PREFIX)" != x ]; then \
	  echo "let krmllib_dir = \"$(PREFIX)/lib/krml\";;" > $@; \
	  echo "let runtime_dir = \"$(PREFIX)/lib/krml/runtime\";;" >> $@; \
	  echo "let include_dir = \"$(PREFIX)/include/\";;" >> $@; \
	  echo "let misc_dir = \"$(PREFIX)/share/krml/misc/\";;" >> $@; \
	else \
	  echo "let krmllib_dir = \"\";;" > $@; \
	  echo "let runtime_dir = \"\";;" >> $@; \
	  echo "let include_dir = \"\";;" >> $@; \
	  echo "let misc_dir = \"\";;" >> $@; \
	fi

.PHONY: src/Version.ml
src/Version.ml:
	@echo "let version = \"$(shell git rev-parse HEAD)\"" > $@ \

clean:
	rm -rf krml _build Karamel.$(FLAVOR)
	$(MAKE) -C test clean
	$(MAKE) -C krmllib clean

test: all
	+$(MAKE) -C test

# Auto-detection
pre:
	@ocamlfind query fstar.lib >/dev/null 2>&1 || \
	  { echo "Didn't find fstar.lib via ocamlfind or in FSTAR_HOME (which is: $(FSTAR_HOME)); run $(MAKE) -C $(FSTAR_HOME)"; exit 1; }


install: all
	@if [ x"$(PREFIX)" = x ]; then echo "please define PREFIX"; exit 1; fi
	mkdir -p $(PREFIX)/bin
	cp _build/src/Karamel.native $(PREFIX)/bin/krml
	mkdir -p $(PREFIX)/include
	cp -r include/* $(PREFIX)/include
	mkdir -p $(PREFIX)/lib/krml
	cp -r krmllib/* $(PREFIX)/lib/krml
	mkdir -p $(PREFIX)/lib/krml/runtime
	cp -r runtime/* $(PREFIX)/lib/krml/runtime
	mkdir -p $(PREFIX)/share/krml/examples
	cp -r test/*.fst $(PREFIX)/share/krml/examples
	mkdir -p $(PREFIX)/share/krml/misc
	cp -r misc/* $(PREFIX)/share/krml/misc

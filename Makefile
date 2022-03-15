# make src/Ast.processed.ml
include $(shell ocamlfind query visitors)/Makefile.preprocess

.PHONY: all minimal clean test

OCAMLBUILD=ocamlbuild -I src -I lib -I parser -I kremlib -use-menhir -use-ocamlfind -classic-display \
 -menhir "menhir --infer --explain"
FLAVOR?=native
TARGETS=Kremlin.$(FLAVOR)
EXTRA_TARGETS=Ast.inferred.mli kremlib/C.cmx kremlib/TestLib.cmx kremlib/C.cmo kremlib/TestLib.cmo

ifeq ($(OS),Windows_NT)
  OCAMLPATH_SEP=;
else
  OCAMLPATH_SEP=:
endif

all: minimal pre kremlib
	OCAML_ERROR_STYLE="short" \
	OCAMLPATH="$(OCAMLPATH)$(OCAMLPATH_SEP)$(FSTAR_HOME)/bin" $(OCAMLBUILD) $(EXTRA_TARGETS)

minimal: src/AutoConfig.ml
	@# Workaround Windows bug in OCamlbuild
	$(shell [ -f Kremlin.$(FLAVOR) ] && rm Kremlin.$(FLAVOR))
	OCAML_ERROR_STYLE="short" $(OCAMLBUILD) $(TARGETS)
	ln -sf Kremlin.$(FLAVOR) krml

kremlib: minimal
	$(MAKE) -C kremlib

src/AutoConfig.ml:
	@if [ x"$(PREFIX)" != x ]; then \
	  echo "let kremlib_dir = \"$(PREFIX)/lib/kremlin\";;" > $@; \
	  echo "let runtime_dir = \"$(PREFIX)/lib/kremlin/runtime\";;" >> $@; \
	  echo "let include_dir = \"$(PREFIX)/include/\";;" >> $@; \
	  echo "let misc_dir = \"$(PREFIX)/share/kremlin/misc/\";;" >> $@; \
	else \
	  echo "let kremlib_dir = \"\";;" > $@; \
	  echo "let runtime_dir = \"\";;" >> $@; \
	  echo "let include_dir = \"\";;" >> $@; \
	  echo "let misc_dir = \"\";;" >> $@; \
	fi

clean:
	rm -rf krml _build Kremlin.$(FLAVOR)
	$(MAKE) -C test clean
	$(MAKE) -C kremlib clean

test: all
	+$(MAKE) -C test

# Auto-detection
pre:
	@command -v fstar.exe >/dev/null 2>&1 || [ -x $(FSTAR_HOME)/bin/fstar.exe ] || \
	  { echo "Didn't find fstar.exe in the path or in FSTAR_HOME (which is: $(FSTAR_HOME))"; exit 1; }
	@ocamlfind query fstarlib >/dev/null 2>&1 || [ -f $(FSTAR_HOME)/bin/fstarlib/fstarlib.cmxa ] || \
	  { echo "Didn't find fstarlib via ocamlfind or in FSTAR_HOME (which is: $(FSTAR_HOME)); run $(MAKE) -C $(FSTAR_HOME)/ulib/ml"; exit 1; }

install: all
	@if [ x"$(PREFIX)" = x ]; then echo "please define PREFIX"; exit 1; fi
	mkdir -p $(PREFIX)/bin
	cp _build/src/Kremlin.native $(PREFIX)/bin/krml
	mkdir -p $(PREFIX)/include
	cp -r include/* $(PREFIX)/include
	mkdir -p $(PREFIX)/lib/kremlin
	cp -r kremlib/* $(PREFIX)/lib/kremlin
	mkdir -p $(PREFIX)/lib/kremlin/runtime
	cp -r runtime/* $(PREFIX)/lib/kremlin/runtime
	mkdir -p $(PREFIX)/share/kremlin/examples
	cp -r test/*.fst $(PREFIX)/share/kremlin/examples
	mkdir -p $(PREFIX)/share/kremlin/misc
	cp -r misc/* $(PREFIX)/share/kremlin/misc

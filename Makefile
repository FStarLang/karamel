# make src/Ast.processed.ml
include $(shell ocamlfind query visitors)/Makefile.preprocess

.PHONY: all minimal clean test pre extra krmllib install

ifeq ($(OS),Windows_NT)
  OCAMLPATH_SEP=;
else
  OCAMLPATH_SEP=:
endif

all: minimal krmllib extra

extra: pre krmllib
	+ OCAML_ERROR_STYLE="short" \
	OCAMLPATH="$(OCAMLPATH)$(OCAMLPATH_SEP)$(FSTAR_HOME)/bin" $(MAKE) -C krmllib extra

minimal: src/AutoConfig.ml
	+ OCAML_ERROR_STYLE="short" $(MAKE) -C src
	ln -sf src/_build/default/Karamel.exe krml

krmllib: minimal
	+$(MAKE) -C krmllib

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
	rm -rf krml
	$(MAKE) -C src clean
	$(MAKE) -C krmllib clean
	$(MAKE) -C test clean

test: all
	+$(MAKE) -C test

# Auto-detection
pre:
	@which fstar.exe >/dev/null 2>&1 || [ -x $(FSTAR_HOME)/bin/fstar.exe ] || \
	  { echo "Didn't find fstar.exe in the path or in FSTAR_HOME (which is: $(FSTAR_HOME))"; exit 1; }
	@ocamlfind query fstarlib >/dev/null 2>&1 || [ -f $(FSTAR_HOME)/bin/fstarlib/fstarlib.cmxa ] || \
	  { echo "Didn't find fstarlib via ocamlfind or in FSTAR_HOME (which is: $(FSTAR_HOME)); run $(MAKE) -C $(FSTAR_HOME)/ulib/ml"; exit 1; }


install: all
	@if [ x"$(PREFIX)" = x ]; then echo "please define PREFIX"; exit 1; fi
	mkdir -p $(PREFIX)/bin
	cp src/_build/default/Karamel.exe $(PREFIX)/bin/krml
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

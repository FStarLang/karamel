# Including a Makefile from the visitors package, but making sure
# to give decent errors.

# make src/Ast.processed.ml
_:=$(shell ocamlfind query)
ifneq ($(.SHELLSTATUS),0)
_: $(error "'ocamlfind query' failed, please install OCaml and put it in your PATH)
endif
visitors_root:=$(shell ocamlfind query visitors)
ifneq ($(.SHELLSTATUS),0)
_: $(error "'ocamlfind query visitors' failed, please 'opam install visitors')
endif
include $(visitors_root)/Makefile.preprocess

.PHONY: all minimal clean test pre krmllib install

ifeq ($(OS),Windows_NT)
  OCAMLPATH_SEP=;
else
  OCAMLPATH_SEP=:
endif

all: minimal krmllib

# If we are just trying to do a minimal build, we don't need F*.
ifneq ($(MAKECMDGOALS),minimal)
include locate_fstar.mk
export OCAMLPATH := $(OCAMLPATH)$(OCAMLPATH_SEP)$(shell $(FSTAR_EXE) --locate_ocaml)
endif

minimal: lib/AutoConfig.ml lib/Version.ml
	dune build
	ln -sf _build/default/src/Karamel.exe krml

krmllib: minimal
	$(MAKE) -C krmllib

lib/AutoConfig.ml:
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
lib/Version.ml:
	@echo "let version = \"$(shell git rev-parse HEAD || echo ${GIT_REV})\"" > $@

clean:
	rm -rf krml
	$(MAKE) -C src clean
	$(MAKE) -C krmllib clean
	$(MAKE) -C test clean

test: all
	$(MAKE) -C test

# Auto-detection
pre:
	@ocamlfind query fstar.lib >/dev/null 2>&1 || \
	  { echo "Didn't find fstar.lib via ocamlfind; is F* properly installed? (FSTAR_EXE = $(FSTAR_EXE))"; exit 1; }


install: all
	@if [ x"$(PREFIX)" = x ]; then echo "please define PREFIX"; exit 1; fi
	mkdir -p $(PREFIX)/bin
	cp _build/default/src/Karamel.exe $(PREFIX)/bin/krml
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

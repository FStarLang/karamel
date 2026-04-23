# make src/Ast.processed.ml
include visitors.mk

.PHONY: all minimal clean test pre krmllib install

FSTAR_EXE ?= fstar.exe

all: local-install

# If we are just trying to do a minimal build, we don't need F*.
# Note: lazy assignment so this does not warn if fstar.exe is not there
# (e.g. on a minimal build or cleaning)
FSTAR_OCAMLENV = $(shell $(FSTAR_EXE) --ocamlenv)

# Creates a top-level ./krml symlink to the built Karamel executable. But, does
# not build krmllib nor is set up in a way that allows karamel to find its
# runtime/misc/include directories, so it is somewhat barebones.
minimal: lib/Version.ml
	dune build
	ln -sf _build/default/src/Karamel.exe krml

krmllib: minimal
	@# Make sure krml can find its relevant directories, since
	@# it is not yet installed with them.
	env \
	  KRML_LIBDIR=$(CURDIR)/krmllib \
	  KRML_INCLUDEDIR=$(CURDIR)/include \
	  KRML_MISCDIR=$(CURDIR)/misc \
	  $(MAKE) -C krmllib

# A full local install. out/ will contain essentially the same directory
# as an OPAM install or binary package.
local-install: krmllib
	$(MAKE) PREFIX=$(CURDIR)/out _install
	ln -sf out/bin/krml krml

.PHONY: lib/Version.ml
lib/Version.ml:
	@echo "let version = \"$(shell git rev-parse HEAD || echo ${GIT_REV})\"" > $@

clean:
	rm -rf krml
	$(MAKE) -C src clean
	$(MAKE) -C krmllib clean
	$(MAKE) -C test clean

test: all
	$(MAKE) -C test

# This depends on minimal since fstar2 (with Pulse) is not expected
# to be able to build krmllib.
test-pulse: minimal
	$(MAKE) -C test/pulse

# Auto-detection
pre:
	@eval "$(FSTAR_OCAMLENV)" && \
	ocamlfind query fstar.lib >/dev/null 2>&1 || \
	  { echo "Didn't find fstar.lib via ocamlfind; is F* properly installed? (FSTAR_EXE = $(FSTAR_EXE))"; exit 1; }

install: all
	$(MAKE) _install

_install:
	@if [ x"$(PREFIX)" = x ]; then echo "please define PREFIX"; exit 1; fi
	mkdir -p $(PREFIX)/bin
	install _build/default/src/Karamel.exe $(PREFIX)/bin/krml
	mkdir -p $(PREFIX)/include/krml
	cp -r include/* $(PREFIX)/include/krml
	mkdir -p $(PREFIX)/lib/krml
	cp -r krmllib/* $(PREFIX)/lib/krml
	echo 'obj' >> $(PREFIX)/lib/krml/fstar.include
	@# ^ So users can just --include lib/krml and also see the checked files.
	mkdir -p $(PREFIX)/share/krml/examples
	cp -r test/*.fst $(PREFIX)/share/krml/examples
	mkdir -p $(PREFIX)/share/krml/misc
	cp -r misc/* $(PREFIX)/share/krml/misc

package: krml.tar.gz

krml.tar.gz:
	$(MAKE) _install PREFIX=$(CURDIR)/pkgtmp/krml
	tar czf krml.tar.gz -C pkgtmp .
	rm -rf pkgtmp

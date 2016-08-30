.PHONY: all tags clean test

OCAMLBUILD=ocamlbuild -I src -I lib -I parser -use-menhir -use-ocamlfind -classic-display
FLAVOR?=native
TARGETS=Kremlin.$(FLAVOR) Tests.$(FLAVOR)

all:
	@# Workaround Windows bug in OCamlbuild
	$(shell [ -f Kremlin.$(FLAVOR) ] && rm Kremlin.$(FLAVOR); [ -f Tests.$(FLAVOR) ] && rm Tests.$(FLAVOR))
	$(OCAMLBUILD) $(TARGETS)
	ln -sf Kremlin.$(FLAVOR) krml

clean:
	rm -rf krml _build test/*.o Tests.$(FLAVOR) Kremlin.$(FLAVOR)

tags:
	ctags -R --exclude=_build .

test: all
	./Tests.native
	$(MAKE) -C test

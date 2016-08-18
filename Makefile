.PHONY: all tags clean test

OCAMLBUILD=ocamlbuild -I src -I lib -use-ocamlfind -classic-display
TARGETS=Kremlin.native Tests.native

all:
	@# Workaround Windows bug in OCamlbuild
	$(shell [ -f Kremlin.native ] && rm Kremlin.native; [ -f Tests.native ] && rm Tests.native)
	$(OCAMLBUILD) $(TARGETS)
	ln -sf Kremlin.native krml

clean:
	rm -rf krml _build test/*.o

tags:
	ctags -R --exclude=_build .

test: all
	./Tests.native
	cd test && ./driver.sh

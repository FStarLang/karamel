OCAMLBUILD=ocamlbuild -I src -I lib -package zarith -package pprint -package unix
TARGETS=Kremlin.native Tests.native

all:
	@# Workaround Windows bug in OCamlbuild
	@-rm $(TARGETS)
	$(OCAMLBUILD) $(TARGETS)

clean:
	$(OCAMLBUILD) -clean

tags:
	ctags -R .

test: all
	./Tests.native
	cd test && ./driver.sh

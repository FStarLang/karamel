OCAMLBUILD=ocamlbuild -I src -I lib -package zarith -package pprint -package unix
TARGETS=Kremlin.native Tests.native

all:
	@# Workaround Windows bug in OCamlbuild
	@-rm $(TARGETS)
	$(OCAMLBUILD) $(TARGETS)
	ln -sf Kremlin.native krml

clean:
	$(OCAMLBUILD) -clean
	rm -f krml

tags:
	ctags -R .

test: all
	./Tests.native
	cd test && ./driver.sh

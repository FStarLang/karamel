OCAMLBUILD=ocamlbuild -I src -I lib -package zarith -package pprint -package unix

all:
	@# Workaround Windows bug in OCamlbuild
	@-rm Kremlin.native
	$(OCAMLBUILD) Kremlin.native

clean:
	$(OCAMLBUILD) -clean

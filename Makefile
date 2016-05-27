OCAMLBUILD=ocamlbuild -I src -package zarith

all:
	# Workaround Windows bug in OCamlbuild
	-@rm Kremlin.native
	$(OCAMLBUILD) Kremlin.native

clean:
	$(OCAMLBUILD) -clean

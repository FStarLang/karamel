OCAMLBUILDFLAGS=-I src -package zarith

all:
	ocamlbuild $(OCAMLBUILDFLAGS) Kremlin.native

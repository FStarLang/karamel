.PHONY: all tags clean test

OCAMLBUILD=ocamlbuild -I src -I lib -I parser -use-menhir -use-ocamlfind -classic-display \
 -menhir "menhir --infer --explain"
FLAVOR?=native
TARGETS=Kremlin.$(FLAVOR) Tests.$(FLAVOR) .docdir/graph.dot
SED=$(shell which gsed >/dev/null 2>&1 && echo gsed || echo sed)

all:
	@# Workaround Windows bug in OCamlbuild
	$(shell [ -f Kremlin.$(FLAVOR) ] && rm Kremlin.$(FLAVOR); [ -f Tests.$(FLAVOR) ] && rm Tests.$(FLAVOR))
	$(OCAMLBUILD) $(TARGETS)
	ln -sf Kremlin.$(FLAVOR) krml

graph: all
	$(SED) -i 's/rotate=90;//g' -- _build/.docdir/graph.dot
	dot -Tsvg _build/.docdir/graph.dot > graph.svg
	$(SED) -i 's/^<text\([^>]\+\)>\([^<]\+\)/<text\1><a xlink:href="\2.html" target="_parent">\2<\/a>/' graph.svg
	$(SED) -i 's/Times Roman,serif/DejaVu Sans, Helvetica, sans/g' graph.svg

clean:
	rm -rf krml _build Tests.$(FLAVOR) Kremlin.$(FLAVOR)
	make -C test clean

tags:
	ctags -R --exclude=_build .

test: all
	./Tests.native
	+make -C test

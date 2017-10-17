.PHONY: all tags clean test _build/.docdir/graph.dot

OCAMLBUILD=ocamlbuild -I src -I lib -I parser -use-menhir -use-ocamlfind -classic-display \
 -menhir "menhir --infer --explain"
FLAVOR?=native
TARGETS=Kremlin.$(FLAVOR) Tests.$(FLAVOR)
SED=$(shell which gsed >/dev/null 2>&1 && echo gsed || echo sed)

all:
	@# Workaround Windows bug in OCamlbuild
	$(shell [ -f Kremlin.$(FLAVOR) ] && rm Kremlin.$(FLAVOR); [ -f Tests.$(FLAVOR) ] && rm Tests.$(FLAVOR))
	$(OCAMLBUILD) $(TARGETS)
	ln -sf Kremlin.$(FLAVOR) krml

_build/.docdir/graph.dot:
	$(OCAMLBUILD) .docdir/graph.dot

graph.svg: _build/.docdir/graph.dot
	$(SED) -i 's/rotate=90;//g' -- $<
	dot -Tsvg $< > $@
	$(SED) -i 's/^<text\([^>]\+\)>\([^<]\+\)/<text\1><a xlink:href="\2.html" target="_parent">\2<\/a>/' $@
	$(SED) -i 's/Times Roman,serif/DejaVu Sans, Helvetica, sans/g' $@

clean:
	rm -rf krml _build Tests.$(FLAVOR) Kremlin.$(FLAVOR)
	make -C test clean

tags:
	ctags -R --exclude=_build .

test: all
	./Tests.native
	+make -C test

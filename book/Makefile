# Minimal makefile for Sphinx documentation
#

# You can set these variables from the command line.
SPHINXOPTS    = -W
SPHINXBUILD   = sphinx-build
SPHINXPROJ    = TheKaRaMeLusermanual
SOURCEDIR     = .
BUILDDIR      = _build

# Put it first so that "make" without argument is like "make help".
help:
	@$(SPHINXBUILD) -M help "$(SOURCEDIR)" "$(BUILDDIR)" $(SPHINXOPTS) $(O)

.PHONY: help Makefile

%.rst: %.fst fst2rst.ml
	ocaml fst2rst.ml < $< > $@

%.rst: %.fsti fst2rst.ml
	ocaml fst2rst.ml < $< > $@

DIRS=tutorial/specs tutorial/code .

all-rst: $(patsubst %.fst,%.rst,$(wildcard $(addsuffix /*.fst,$(DIRS))))

all-rsti: $(patsubst %.fsti,%.rst,$(wildcard $(addsuffix /*.fsti,$(DIRS))))

_static:
	mkdir -p $@

prep: all-rst all-rsti _static

# Catch-all target: route all unknown targets to Sphinx using the new
# "make mode" option.  $(O) is meant as a shortcut for $(SPHINXOPTS).
html: Makefile prep
	@$(SPHINXBUILD) -M $@ "$(SOURCEDIR)" "$(BUILDDIR)" $(SPHINXOPTS) $(O)

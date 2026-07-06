# Including a Makefile from the visitors package, but making sure
# to give decent errors.

_ := $(shell ocamlfind query)
ifneq ($(.SHELLSTATUS),0)
$(error "'ocamlfind query' failed, please install OCaml and put it in your PATH)
endif

visitors_root := $(shell ocamlfind query visitors)
ifneq ($(.SHELLSTATUS),0)
$(error "'ocamlfind query visitors' failed, please 'opam install visitors')
endif
include $(visitors_root)/Makefile.preprocess

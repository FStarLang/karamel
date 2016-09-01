# A minimalistic Makefile for calling Kremlin... KOPTS is for user-defined flags
# (e.g. -verbose).
OPTS=-tmpdir out $(KOPTS)
TESTOPTS=$(OPTS) -add-include '"testlib.h"' -I . testlib.c
KRML=../krml

all: Hoisting.exe Flat.exe Renaming.exe Vla.exe Inline.exe \
  Poly1305.exe Chacha20.exe Aead.exe
	for f in $^; do echo $$f; ./$$f; done

# Standalone test files that have a main in F* (hence -no-prefix)
%.exe: %.fst
	$(KRML) $(TESTOPTS) -no-prefix $* -o $@ $<

# Test files that have an "external" main written by hand...
Poly1305.exe: main-Poly1305.c testlib.c
	$(KRML) --lax $(OPTS) Crypto.Symmetric.Poly1305.fst $^ -o $@

Chacha20.exe: main-Chacha.c testlib.c
	$(KRML) --lax $(OPTS) Crypto.Symmetric.Chacha20.fst $^ -o $@

Aead.exe: main-Aead.c testlib.c
	$(KRML) --lax $(OPTS) Crypto.AEAD.Chacha20Poly1305.fst $^ -o $@

FIND=$(shell which gfind >/dev/null 2>/dev/null && echo "gfind" || echo "find")

clean:
	$(FIND) out -\( -not -iname '.gitignore' -and -type f -\) -delete
	$(FIND) . -\( -iname '*.exe' -or -iname 'out.krml' -\) -delete

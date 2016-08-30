OPTS=-tmpdir out
TESTOPTS=$(OPTS) -add-include '"testlib.h"' -I . testlib.c
KRML=../krml

all: Hoisting.test Flat.test Renaming.test Vla.test

%.test: %.fst
	$(KRML) $(TESTOPTS) -no-prefix $* -o $*.exe $(KOPTS) $<
	./$*.exe



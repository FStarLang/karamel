.PHONY: %

all: b/dist/B.exe
	$<

a/dist/A.h: $(wildcard a/*.fst)
	+$(MAKE) -C a

b/dist/B.exe: a/dist/A.h b/B.fst
	+$(MAKE) -C b

clean:
	+$(MAKE) -C b clean || true
	+$(MAKE) -C a clean

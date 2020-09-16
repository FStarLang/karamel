all: b/dist/B.exe

a/dist/A.h: a/A.fst
	+$(MAKE) -C a

b/dist/B.exe: a/dist/A.h b/B.fst
	+$(MAKE) -C b

clean:
	+$(MAKE) -C b clean || true
	+$(MAKE) -C a clean

.PHONY: all clean

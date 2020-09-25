.PHONY: all a b clean

all: b

a:
	+$(MAKE) -C a

b: a
	+$(MAKE) -C b

clean:
	+$(MAKE) -C b clean || true
	+$(MAKE) -C a clean

.PHONY: all clean

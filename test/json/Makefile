include ../../Makefile.common

KRML_BIN = ../../_build/default/src/Karamel.exe
KRML = $(KRML_BIN)

OUTPUT_DIR = .output

JSON_FILES = $(wildcard *.json)
TESTS = $(patsubst %.json,%.test,$(JSON_FILES))

all: $(TESTS)

.PRECIOUS: $(OUTPUT_DIR)/%.exe
$(OUTPUT_DIR)/%.exe: %.json $(KRML_BIN) | $(OUTPUT_DIR)
	$(call run-with-log, \
	  $(KRML) -tmpdir $(subst .exe,.out,$@) -no-prefix $* \
	    -o $@ $< \
	,[JSON_KRML] $*,$(OUTPUT_DIR)/$*)

$(OUTPUT_DIR):
	mkdir -p $@

%.test: $(OUTPUT_DIR)/%.exe
	@$^ && echo -e "\033[01;32m✔\033[00m [JSON_TEST,$*]" || (echo -e "\033[01;31m✘\033[00m [JSON_TEST,$*]" && false)

clean:
	rm -rf $(OUTPUT_DIR)

.PHONY: all clean

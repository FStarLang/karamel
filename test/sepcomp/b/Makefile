#############################
# This is the main Makefile #
#############################

# This tutorial assumes you have a degree of familiarity with GNU make,
# including automatic variables such as $@, $< and $^. Some mandatory reading if
# you are not fluent in GNU make:
# - https://www.gnu.org/software/make/manual/html_node/Automatic-Variables.html#Automatic-Variables
# - https://www.gnu.org/software/make/manual/html_node/Pattern-Intro.html#Pattern-Intro
# - https://www.gnu.org/software/make/manual/html_node/Pattern_002dspecific.html#Pattern_002dspecific

# I usually prefer to rule out OSX make on the basis that it doesn't have the
# shortest stem rule, which is incredibly useful.
ifeq (3.81,$(MAKE_VERSION))
  $(error You seem to be using the OSX antiquated Make version. Hint: brew \
    install make, then invoke gmake instead of make)
endif




# Main entry points (first one is default)
# ----------------------------------------

all: dist/B.exe

include Makefile.include

# Definition of F* flags
# ----------------------

# Some reasonable flags to turn on:
# - 247: checked file not written because some of its dependencies...
# - 285: missing or file not found, almost always something to act on
# - 241: stale dependencies, almost always a sign that the build is incorrect
#
# But also:
# - --cmi, for cross-module inlining, a must-have for anyone who relies on
#   inline_for_extraction in the presence of interfaces
# - --cache_checked_modules to rely on a pre-built ulib and krmllib
# - --cache_dir, to avoid polluting our generated build artifacts outside o

FSTAR_EXE ?= fstar.exe
FSTAR_NO_FLAGS = $(FSTAR_EXE) \
  --odir obj --cache_checked_modules $(FSTAR_INCLUDES) --cmi \
  --already_cached 'Prims FStar LowStar C Spec.Loops TestLib WasmSupport A' --warn_error '+241@247+285' \
  --cache_dir obj

# Initial dependency analysis
# ---------------------------

# Important to wildcard both fst and fsti since there are fstis without fsts,
# etc. Note that I'm using wildcard rather than assume $(SHELL) is bash and has
# fancy globbing rules -- particularly true on Windows.
FSTAR_ROOTS = $(wildcard $(addsuffix /*.fsti,$(SOURCE_DIRS))) \
  $(wildcard $(addsuffix /*.fst,$(SOURCE_DIRS))) \


# This is the only bulletproof way that I know of forcing a regeneration of the
# .depend file every single time. Why, you may ask? Well, it's frequent enough
# to add a new file that you don't want to decipher a cryptic error only to
# remember you should run `make depend`. Also, if you move files around, it's
# good to force regeneration even though .depend may be more recent than the
# mtime of the moved files.
ifndef MAKE_RESTARTS
obj/.depend: .FORCE
	mkdir -p obj
	$(FSTAR_NO_FLAGS) --dep full $(notdir $(FSTAR_ROOTS)) $(FSTAR_EXTRACT) --output_deps_to $@

.PHONY: .FORCE
.FORCE:
endif

include obj/.depend

# Verification
# ------------

# Everest-specific idiom: all makefiles accept OTHERFLAGS, for instance, if one
# wants to rebuild with OTHERFLAGS="--admit_smt_queries true". We just don't
# pass such flags to the dependency analysis.
FSTAR = $(FSTAR_NO_FLAGS) $(OTHERFLAGS)

# Creating these directories via a make rule, rather than rely on F* creating
# them, as two calls to F* might race.
obj:
	mkdir $@

# We allow some specific pattern rules to be added here, relying on the shortest
# stem rule for them to take precedence. For instance, you may want to do:
#
# obj/Bignum.Impl.fst.checked: FSTAR_FLAGS = "--query_stats"
#
# (Note: for options that control the SMT encoding, such as
# --smtencoding.nl_arith_repr native, please make sure you also define them in
# Makefile.common for %.fst-in otherwise you'll observe different behaviors
# between interactive and batch modes.)
#
# By default, however, variables are inherited through the dependencies, meaning
# that the example above would normally set these FSTAR_FLAGS for any .checked
# that is rebuilt because it's a dependency of Bignum.Impl.fst.checked.
#
# To avoid this unpleasant behavior, the most general pattern rule (longest
# stem) also defines a suitable default value for FSTAR_FLAGS.
%.checked: FSTAR_FLAGS=

# Note: F* will not change the mtime of a checked file if it is
# up-to-date (checksum matches, file unchanged), but this will confuse
# make and result in endless rebuilds. So, we touch that file.
%.checked: | obj
	$(FSTAR) $< $(FSTAR_FLAGS) && touch -c $@

# Extraction
# ----------

# A few mismatches here between the dependencies present in the .depend and the
# expected F* invocation. In .depend:
#
# obj/Bignum_Impl.ml: obj/Bignum.Impl.fst.checked ... more dependencies ...
#
# But F* wants (remember that F* searches for source files anywhere on the
# include path):
#
# fstar Bignum.Impl.fst --extract_module BigNum.Impl
#
# We use basename because we may also extract krml files from .fsti.checked
# files (not true for OCaml, we don't extract mlis from fstis).
.PRECIOUS: obj/%.ml
obj/%.ml:
	$(FSTAR) $(notdir $(subst .checked,,$<)) --codegen OCaml \
	--extract_module $(basename $(notdir $(subst .checked,,$<)))

.PRECIOUS: obj/%.krml
obj/%.krml:
	$(FSTAR) $(notdir $(subst .checked,,$<)) --codegen krml \
	--extract_module $(basename $(notdir $(subst .checked,,$<)))

# F* --> C
# --------

KRML=$(KRML_HOME)/krml -fstar $(FSTAR_EXE)

# Note: the implementation of the intrinsic uses external linkage, but you could
# easily turn this file into a .h, use -add-include '"Impl_Bignum_Intrinsics.h"'
# and pass -static-header Impl.Bignum.Intrinsics as described in the
# documentation.
HAND_WRITTEN_C_FILES = 

# This is now the preferred and recommended way to compile C code with KaRaMeL.
#
# KaRaMeL (via -skip-compilation) only generates a stub Makefile in dist/,
# instead of acting as a C compilation driver like it did before. The Makefile
# that is generated by KaRaMeL is basic, but takes into account:
# - the -o option to determine what is being built
# - the C files passed on the command line, which will be linked together
# - C compiler flags passed to KaRaMeL via -ccopts
#
# This Makefile is called Makefile.basic and should be enough for all your basic
# needs. If you need something more fancy, you can easily author your own custom
# dist/Makefile, which includes Makefile.basic, then proceeds to redefine /
# tweak some variables.
#
# Note that you are of course more than welcome to define your own
# CMakeLists.txt or whatever your favorite build system is: this tutorial only
# describes the supported canonical way of compiling code.
#
# See the advanced topics section for an in-depth explanation of how the -bundle
# option works. We also use -minimal.
dist/Makefile.basic: $(filter-out %prims.krml,$(ALL_KRML_FILES))
	mkdir -p $(dir $@)
	$(KRML) -tmpdir $(dir $@) -skip-compilation \
	  $(filter %.krml,$^) \
	  -warn-error @4@5@18 \
	  -fparentheses \
	  -static-header A.Base \
	  -library A.* \
	  -bundle 'B=A.*,FStar.*,LowStar.*,Prims,C' \
	  -bundle 'D=A.*,FStar.*,LowStar.*,Prims,C' \
	  -bundle 'A.*[rename=A,rename-prefix]' \
	  -no-prefix B \
	  -minimal \
	  -add-include '"A.h"' \
	  -o B.exe
	! test -e dist/A.h

dist/B.exe: dist/Makefile.basic
	$(MAKE) -C $(dir $@) -f $(notdir $<) USER_CFLAGS=-I$(realpath ../a/dist)
	$@

.DELETE_ON_ERROR: dist/B.exe

clean:
	rm -rf obj dist *~

.PHONY: all clean

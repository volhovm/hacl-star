print-%: ; @echo $* is $($*)

# ROOTS = $(wildcard $(addsuffix /*.fsti,$(DIRS)) $(addsuffix /*.fst,$(DIRS)))

test: test-c test-ml
test-c: test-c-Hacl_Test_SHA3 test-c-Hacl_Test_CSHAKE
test-ml: $(subst .,_,$(patsubst %.fst,test-ml-%,$(notdir $(wildcard specs/tests/*.fst))))

ROOTS = ./code/sha3/Hacl.Test.SHA3.fst \
    ./code/sha3/Hacl.Test.CSHAKE.fst \
	./specs/tests/Spec.SHA3.Test.fst \
    ./lib/Lib.PrintBuffer.fsti \
    ./lib/Lib.RandomBuffer.fsti \
    # ./code/experimental/curve25519/Hacl.Curve25519_51.fst


include Makefile.common

ifndef MAKE_RESTARTS
.depend: .FORCE
	@$(FSTAR_NO_FLAGS) --dep full $(ROOTS) > $@
.PHONY: .FORCE
.FORCE:
endif

include .depend

SPEC_FILES          = $(addprefix $(HACL_HOME)/specs/Spec., SHA3.fst)
SPEC_CHECKED_FILES	= $(addsuffix .checked, $(SPEC_FILES))

%.checked:
	$(FSTAR) $< && \
	touch $@

.PRECIOUS: %.krml

$(OUTPUT_DIR)/%.krml:
	$(FSTAR) --codegen Kremlin \
	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	  $(notdir $(subst .checked,,$<)) && \
	touch $@

COMPACT_FLAGS=-bundle Hacl.Impl.SHA3+Hacl.SHA3=[rename=Hacl_SHA3] \
   -bundle Prims \
   -bundle LowStar.* \
   -bundle C,C.String,C.Loops,Spec.Loops,C.Endianness,FStar.*[rename=Hacl_Kremlib] \
   -bundle 'Test.*,WindowsHack' \
   -minimal \
   -add-include '"kremlin/internal/types.h"' \
   -add-include '"kremlin/internal/target.h"' \
   -add-include '"kremlin/c_endianness.h"' \
   -add-include '<string.h>' \
   -fno-shadow -fcurly-braces

 HAND_WRITTEN_C	= Lib.PrintBuffer Lib.RandomBuffer
 HAND_WRITTEN_FILES = $(wildcard $(LIB_DIR)/c/*.c)
 DEFAULT_FLAGS	= $(addprefix -library ,$(HAND_WRITTEN_C)) \
   -bundle Lib.*[rename=Hacl_Lib] -bundle Hacl.Test.*

dist/compact/Makefile.basic: EXTRA=$(COMPACT_FLAGS)

.PRECIOUS: dist/compact/Makefile.basic
dist/%/Makefile.basic: $(ALL_KRML_FILES) dist/headers/Makefile.basic $(HAND_WRITTEN_FILES) # | old-extract-c
	mkdir -p $(dir $@)
	cp $(HAND_WRITTEN_FILES) dist/headers/*.h $(dir $@)
	$(KRML) $(DEFAULT_FLAGS) $(EXTRA) \
	  -tmpdir $(dir $@) -skip-compilation \
	  -bundle Spec.*[rename=Hacl_Spec] $(filter %.krml,$^) \
	  -ccopt -Wno-unused \
	  -warn-error @4 \
	  -fparentheses \
	  $(notdir $(HAND_WRITTEN_FILES)) \
	  -o libhacl.a


# Auto-generates headers for the hand-written C files. If a signature changes on
# the F* side, hopefully this will ensure the C file breaks. Note that there's
# no conflict between the headers because this generates
# Lib_Foobar while the run above generates a single Hacl_Lib.
dist/headers/Makefile.basic: $(ALL_KRML_FILES)
	$(KRML) \
	  -tmpdir $(dir $@) -skip-compilation \
	  $(patsubst %,-bundle %=,$(HAND_WRITTEN_C)) \
	  $(patsubst %,-library %,$(HAND_WRITTEN_C)) \
	  -minimal -add-include '"kremlib.h"' \
	  -bundle '\*,WindowsBug' $^

# Auto-generates a single C test file.
.PRECIOUS: dist/test/c/%.c
dist/test/c/%.c: $(ALL_KRML_FILES)
	$(KRML) \
	  -tmpdir $(dir $@) -skip-compilation \
	  -no-prefix $(subst _,.,$*) \
	  -library Hacl,Lib \
	  -fparentheses -fcurly-braces -fno-shadow \
	  -minimal -add-include '"kremlib.h"' \
	  -bundle '*[rename=$*]' $^

compile-%: dist/%/Makefile.basic
	$(MAKE) -C $(dir $<) -f $(notdir $<)


# C tests
.PRECIOUS: dist/test/c/%.exe
dist/test/c/%.exe: dist/test/c/%.c compile-generic
	# Linking with full kremlib since tests may use TestLib, etc.
	$(CC) -Wall -Wextra -Werror -Wno-unused-parameter $< -o $@ dist/generic/libhacl.a \
	  -I $(dir $@) -I $(KREMLIN_HOME)/include \
	  $(KREMLIN_HOME)/kremlib/dist/generic/libkremlib.a

test-c-%: dist/test/c/%.exe
	$<

# Generated test vectors
.PRECIOUS: dist/test/vectors/%.c
dist/test/vectors/%.c: $(ALL_KRML_FILES)
	mkdir -p $(dir $@)
	cp $(HACL_HOME)/test/test-vectors/generated/c/$*.c $(dir $@)/

.gen_tests:
	$(MAKE) -C test/test-vectors .gen-tests

.PRECIOUS: dist/test/vectors/%.exe
dist/test/vectors/%.exe: dist/test/vectors/%.c compile-generic compile-test
	$(CC) -Wall -Wextra -Werror -Wno-unused-parameter $< -o $@ dist/generic/libhacl.a \
	  -I $(dir $@) -I dist/test -I $(KREMLIN_HOME)/include \
	  $(KREMLIN_HOME)/kremlib/dist/generic/libkremlib.a

test-vectors-%: dist/test/vectors/%.exe
	$<

test-vectors: $(patsubst %.c,test-vectors-%,$(notdir $(wildcard test/test-vectors/generated/c/*.c)))

clean-test:
	rm -rf dist/test/vectors
	rm -rf test/test-vectors/generated
	rm -f test/test-vectors/.gen-tests

clean: clean-test
	rm -rf dist


include ../../Makefile.include

BIGNUM= \
	$(HACL_HOME)/code/bignum/Hacl.Spec.Bignum.Field.fst \
	$(HACL_HOME)/code/bignum/Hacl.Bignum.Limb.fst \
	$(HACL_HOME)/code/bignum/Hacl.Bignum.Wide.fst \
	$(HACL_HOME)/code/bignum/Hacl.Spec.Bignum.Bigint.fst \
	$(HACL_HOME)/code/bignum/Hacl.Spec.Bignum.Fsum.fst \
	$(HACL_HOME)/code/bignum/Hacl.Spec.Bignum.Fproduct.fst \
	$(HACL_HOME)/code/bignum/Hacl.Spec.Bignum.Fmul.fst \
	$(HACL_HOME)/code/bignum/Hacl.Bignum.Fsum.fst \
	$(HACL_HOME)/code/bignum/Hacl.Bignum.Fproduct.fst \
	$(HACL_HOME)/code/bignum/Hacl.Bignum.Fmul.fst \

POLY1305_SPECIFIC= \
	Hacl.Bignum.Constants.fst \
	Hacl.Bignum.Parameters.fst \
	Hacl.Spec.Bignum.Modulo.fst \
	Hacl.Bignum.Modulo.fst \
	Hacl.Bignum.AddAndMultiply.fst \
	Hacl.MAC.Poly1305_32.fst \
	Poly1305_32.fst
#	Hacl.Spec.Bignum.AddAndMultiply.fst \
	Hacl.Spec.MAC.Poly1305_32.fst \

SLOW=

TODO=

POLY1305_FILES=$(BIGNUM) $(POLY1305_SPECIFIC)

FSTAR_INCLUDES+=--include$(HACL_HOME)/code/bignum

# Parameter for interactive mode
%.fst-in:
	@echo $(OPTIONS) --hint_info \
	$(FSTAR_INCLUDES)

%.fst-verify: %.fst
	$(FSTAR_HOME)/bin/fstar.exe \
		--include ../lib --include ../../bignum $^ --use_hints

verify: $(addsuffix -verify, $(POLY1305_FILES))

%.fst-hints: %.fst
	$(FSTAR_HOME)/bin/fstar.exe \
		--include ../lib --include ../../bignum $^ --record_hints

hints: $(addsuffix -hints, $(POLY1305_SPECIFIC))

# By default, KreMLin drops a bunch of spec-related module that are not meant to
# extract.
CFLAGS=-Wall -Wextra -Wno-unused-parameter -Wno-unused-variable
KREMLIN_ARGS+=-I $(HACL_HOME)/code/bignum -tmpdir poly-c \
	-bundle 'Hacl.Spec.*,Hacl.Spe.*' -fparentheses \
	-drop Combinators,Hacl.Endianness,Spec.*,Hacl.Bignum.Parameters,Hacl.Endianness,Hacl.Spec,Hacl.Spec.*,Hacl.Spe,Hacl.Spe.*,Hacl.Cast,Hacl.UInt8,Hacl.UInt16,Hacl.UInt32,Hacl.UInt64,Hacl.UInt128,Prims,Seq.* \
	$(KREMLIN_TESTLIB)

poly-c/out.krml: $(POLY1305_FILES) Hacl.Test.Poly1305_32.fst
	$(KREMLIN) $(KREMLIN_ARGS) -skip-translation $^ -o $@

poly-c/Poly1305_32.c: poly-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) $^ \
		-bundle "Hacl.Spec.\*" -bundle "Poly1305_32=Poly1305_32,Hacl.Bignum.\*,Hacl.MAC.\*" \
		-skip-compilation

poly1305.exe: poly-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) \
		-no-prefix Hacl.Test.Poly1305_32 \
		-bundle "Hacl.Spec.\*" -bundle "Poly1305_32=Poly1305_32,Hacl.Bignum.\*,Hacl.MAC.\*" \
		$^ -o $@
	./$@

extract-c: poly-c/Poly1305_32.c

include $(FSTAR_HOME)/src/gmake/fstar.mk
CODEGEN_ARGS=--lax --codegen OCaml --no_location_info $(FSTAR_DEFAULT_ARGS)
OCAMLOPT := $(OCAMLOPT) -w -8-20-26-28-10
POLY_EXTRACTED=Hacl_Bignum_Constants.ml Hacl_Bignum_Parameters.ml Hacl_MAC_Poly1305_64.ml

extract-ml:
	mkdir -p poly-ml
	$(FSTAR) $(CODEGEN_ARGS) --include ../bignum --include ../lib \
	--odir poly-ml $(POLY1305_FILES) \
	--no_extract Hacl.UInt64 --no_extract Hacl.UInt32 --no_extract Hacl.UInt128 --no_extract Hacl.UInt16 --trace_error
	$(OCAMLOPT) -I poly-ml  -I ../lib/ml $(addprefix poly-ml/,$(POLY_EXTRACTED))

compile-ml:
	$(OCAMLOPT) -I poly-ml -I ../lib/ml $(addprefix poly-ml/,$(POLY_EXTRACTED))

clean:
	rm -rf *.exe *.exe.* *.out *~ poly-c

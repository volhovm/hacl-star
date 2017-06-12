FSTAR_HOME?=../../../dependencies/FStar
KREMLIN_HOME?=$(FSTAR_HOME)/../kremlin
include ../../Makefile.include
HACL_HOME=../../..

INCLUDE_DIRS=$(HACL_HOME)/code/bignum $(HACL_HOME)/code/lib/kremlin $(KREMLIN_HOME)/kremlib $(HACL_HOME)/specs

FSTAR_LIB_FILES= \
	FStar.Mul.fst \
	FStar.Squash.fsti \
	FStar.Squash.fst \
	FStar.Classical.fst \
	FStar.StrongExcludedMiddle.fst \
	FStar.PropositionalExtensionality.fst \
	FStar.FunctionalExtensionality.fst \
	FStar.PredicateExtensionality.fst \
	FStar.List.Tot.Base.fst \
	FStar.List.Tot.Properties.fst \
	FStar.List.Tot.fst \
	FStar.Seq.Base.fst \
	FStar.Seq.Properties.fst \
	FStar.Seq.fst \
	FStar.Math.Lib.fst \
	FStar.Math.Lemmas.fst \
	FStar.BitVector.fst \
	FStar.Int.fst \
	FStar.UInt.fst \
	FStar.UInt32.fst \
	FStar.Int32.fst \
	FStar.Int8.fst \
	FStar.Int16.fst \
	FStar.Int63.fst \
	FStar.Int64.fst \
	FStar.Int128.fst \
	FStar.UInt8.fst \
	FStar.UInt16.fst \
	FStar.UInt63.fst \
	FStar.UInt64.fst \
	FStar.UInt128.fst \
	FStar.Int.Cast.fst \
	FStar.TSet.fst \
	FStar.Set.fst \
	FStar.Map.fst \
	FStar.Heap.fst \
	FStar.Ghost.fst \
	FStar.HyperHeap.fst \
	FStar.HyperStack.fst \
	FStar.ST.fst \
	FStar.Buffer.fst

POLY1305_FILES= \
	Hacl.Bignum.Constants.fst \
	Hacl.Bignum.Parameters.fst \
	Hacl.Bignum.Limb.fst \
	Hacl.Bignum.Wide.fst \
	Hacl.Spec.Bignum.Field.fst \
	Hacl.Spec.Bignum.Bigint.fst \
	Hacl.Spec.Bignum.Modulo.fst \
	Hacl.Bignum.Modulo.fst \
	Hacl.Spec.Bignum.Fsum.fst \
	Hacl.Spec.Bignum.Fproduct.fst \
	Hacl.Bignum.Fsum.fst \
	Hacl.Bignum.Fproduct.fst \
	Hacl.Spec.Bignum.AddAndMultiply.fst \
	Hacl.Spec.MAC.Poly1305_64.fst \
	Hacl.MAC.Poly1305_64.fst

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

POLY1305_MODULES= \
	Hacl.Bignum.Parameters \
	Hacl.Bignum.Limb \
	Hacl.Bignum.Wide \
	Hacl.Spec.Bignum.Field \
	Hacl.Spec.Bignum.Bigint \
	Hacl.Bignum.Modulo \
	Hacl.Spec.Bignum.Fsum \
	Hacl.Spec.Bignum.Fproduct \
	Hacl.Bignum.Fsum \
	Hacl.Bignum.Fproduct \
	Hacl.Spec.Bignum.AddAndMultiply \
	Hacl.Spec.MAC.Poly1305_64 \
	Hacl.MAC.Poly1305


%.fst-verify: %.fst
	$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack \
		--include ../lib --include ../../bignum $^ --use_hints

verify: $(addsuffix -verify, $(POLY1305_FILES))

%.fst-hints: %.fst
	$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack \
		--include ../lib --include ../../bignum $^ --record_hints

hints: $(addsuffix -hints, $(POLY1305_SPECIFIC))


# By default, KreMLin drops a bunch of spec-related module that are not meant to
# extract.
INCLUDES=$(addprefix -I , $(INCLUDE_DIRS))
CFLAGS=-Wall -Wextra -Wno-unused-parameter -Wno-unused-variable
KRML_BIN=$(KREMLIN_HOME)/_build/src/Kremlin.native
KRML=$(KRML_BIN) $(KREMLIN_ARGS) $(INCLUDES) -tmpdir poly-c \
  -bundle 'Hacl.Spec.\*' -bundle 'Hacl.Spe.\*' -fparentheses \
  -add-include '"testlib.h"' \
  -drop Combinators,Hacl.Endianness,Spec.*,Hacl.Bignum.Parameters,Hacl.Endianness,Hacl.Spec,Hacl.Spe,Hacl.Cast,Hacl.UInt8,Hacl.UInt16,Hacl.UInt32,Hacl.UInt64,Hacl.UInt128,Prims,FStar,Seq.*

poly-c/Poly1305_32.c: $(POLY1305_SPECIFIC)
	$(KRML) $^ Hacl.Test.Poly1305_32.fst \
		-no-prefix Hacl.Test.Poly1305_32 \
		-bundle "Hacl.Spec.\*" -bundle "Poly1305_32=Poly1305_32,Hacl.Bignum.\*,Hacl.MAC.\*" \
		-skip-compilation

extract-c: poly-c/Poly1305_32.c

poly1305.exe: poly-c/Poly1305_32.c poly-c/Hacl_Test_Poly1305_32.c $(KREMLIN_HOME)/kremlib/kremlib.c $(KREMLIN_HOME)/kremlib/testlib.c
	$(CC) $(INCLUDES) $(CFLAGS) $^ -o $@
	./$@

include $(FSTAR_HOME)/src/gmake/fstar.mk
include $(FSTAR_HOME)/ulib/ml/Makefile.include
CODEGEN_ARGS=--lax --codegen OCaml --no_location_info $(FSTAR_DEFAULT_ARGS)
OCAMLOPT := $(OCAMLOPT) -w -8-20-26-28-10
POLY_EXTRACTED=Hacl_Bignum_Constants.ml Hacl_Bignum_Parameters.ml Hacl_MAC_Poly1305_64.ml

extract-ml:
	mkdir -p poly-ml
	$(FSTAR) $(CODEGEN_ARGS) --include $(FSTAR_HOME)/ulib/hyperstack --include ../bignum --include ../lib \
	--odir poly-ml $(POLY1305_FILES) \
	--no_extract FStar.Math.Lib --no_extract FStar.HyperHeap --no_extract FStar.HyperStack --no_extract FStar.ST --no_extract FStar.Seq --no_extract FStar.UInt128 --no_extract FStar.Int128  --no_extract FStar.Int64 --no_extract FStar.UInt63 --no_extract FStar.Int63 --no_extract FStar.UInt32 --no_extract FStar.Int32 --no_extract FStar.UInt31 --no_extract FStar.Int31 --no_extract FStar.UInt16 --no_extract FStar.Int16 --no_extract FStar.UInt8 --no_extract FStar.Int8 --no_extract Hacl.UInt64 --no_extract Hacl.UInt32 --no_extract Hacl.UInt128 --no_extract Hacl.UInt16 --trace_error 
	$(OCAMLOPT) -I poly-ml  -I ../lib/ml -I $(FSTAR_HOME)/ulib/ml/hyperstack -I $(FSTAR_HOME)/ulib/ml $(addprefix poly-ml/,$(POLY_EXTRACTED)) 

compile-ml:
	$(OCAMLOPT) -I poly-ml -I ../lib/ml -I $(FSTAR_HOME)/ulib/ml/hyperstack -I $(FSTAR_HOME)/ulib/ml $(addprefix poly-ml/,$(POLY_EXTRACTED)) 

clean:
	rm -rf *.exe *.exe.* *.out *~ poly-c

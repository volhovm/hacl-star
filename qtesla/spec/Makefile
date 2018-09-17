include ../../Makefile.include

.PHONY=all test

FSTAR_INCLUDES+= \
	--include $(HACL_HOME)/lib \
	--include $(HACL_HOME)/lib/fst \
	--include $(HACL_HOME)/specs \
	--include $(HACL_HOME)/specs/lemmas \
	--expose_interfaces

SPEC_FILES=	Spec.QTesla.fst

LIBS = Lib.IntTypes.fst Lib.RawIntTypes.fst Lib.Sequence.fst Lib.ByteSequence.fst
LIBS_FILES= $(addprefix ../../lib/fst/, $(LIBS))
LIBS_ML = Lib_IntTypes.ml Lib_RawIntTypes.ml Lib_Sequence.ml Lib_ByteSequence.ml
LIBS_EX = $(addprefix --extract_module , $(LIBS:.fst=))

#
# Main targets
#

hints: $(addsuffix .hints, $(SPEC_FILES))
verify: $(addsuffix -verify, $(SPEC_FILES))

all: test

test: QTesla.exe

clean:
	rm -rf *.cmi *.cmo *.cmx *.o *~ *.out *.exe *-ml

#
# Primitive targets
#

#%.exe: $(LIBS_FILES) Spec.%.fst tests/Spec.%.Test.fst
#	mkdir -p $*-ml
#	$(FSTAR) --codegen OCaml --lax $(LIBS_EX) --extract_module Spec.$* --extract_module Spec.$*.Test --odir $*-ml $^
#	@echo 'let _ = test()' >> $*-ml/Spec_$*_Test.ml
#	$(OCAMLOPT) -I $*-ml $(addprefix $*-ml/, $(LIBS_ML))  $*-ml/Spec_$*.ml $*-ml/Spec_$*_Test.ml -o $*.exe
#	./$*.exe
#

QTesla.exe: $(LIBS_FILES) Spec.QTesla.fst 
	mkdir -p qtesla-ml
	$(FSTAR) --codegen OCaml --lax $(LIBS_EX) --extract-module Spec.QTesla --extract-module Spec.Keccak --extract-module Spec.Frodo.Keccak --odir qtesla-ml $^
	@echo 'let _ = test()' >> qtesla-ml/Spec_QTesla_Test.ml
	$(OCAMLOPT) -I qtesla-ml $(addprefix qtesla-ml/, $(LIBS_ML)) qtesla-ml/Spec_QTesla.ml qtesla-ml/Spec_Keccak.ml qtesla-ml/Spec_Frodo_Keccak.ml -o QTesla.exe


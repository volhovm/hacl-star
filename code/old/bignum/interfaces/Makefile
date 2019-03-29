include ../../Makefile.include

BIGNUM_FILES= \
    Hacl.Bignum.Constants.fsti \
	Hacl.Bignum.Parameters.fsti \
	Hacl.Bignum.Modulo.fsti \
	Hacl.Bignum.Crecip.fsti \
	Hacl.Spec.Bignum.Crecip.fsti \
	Hacl.Spec.Bignum.Modulo.fsti \
	Hacl.Spec.Bignum.Fsquare.fsti \
	Hacl.Bignum.Fsquare.fsti \
	Hacl.Bignum.Fsquare.fsti

FSTAR_INCLUDES+=--include .. --include ../../lib

ct: $(addsuffix -lax, $(BIGNUM_FILES))
verify: $(addsuffix -verify, $(BIGNUM_FILES))
hints: $(addsuffix .hints, $(BIGNUM_FILES))
test:

all-ci: verify
all-ver: verify
all-hints: hints
all-ct: ct

count-line:
	cloc --force-lang=ocaml $(BIGNUM_FILES)

clean:
	rm -rf *.exe *.out *~ x25519/*~ poly1305/*~ interfaces/*~ tmp tmppoly

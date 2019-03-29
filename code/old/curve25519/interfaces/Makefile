include ../../Makefile.include

FILES= Hacl.Curve25519.fsti

FSTAR_INCLUDES+=--include ../../bignum/interfaces --include ../../bignum --include .. --include ../../lib

ct: $(addsuffix -lax, $(FILES))
verify: $(addsuffix -verify, $(FILES))
hints: $(addsuffix .hints, $(FILES))
test:

all-ci: verify
all-ver: verify
all-hints: hints
all-ct: ct

count-line:
	cloc --force-lang=ocaml $(FILES)

clean:
	rm -rf *.exe *.out *~ tmp

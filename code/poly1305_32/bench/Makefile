include ../../Makefile.include

TWEETNACL_HOME?=../../../other_providers/tweetnacl
OPENSSL_HOME?=../../../other_providers/openssl
LIBSODIUM_HOME ?=../../../other_providers/libsodium/src/libsodium

CC?=gcc-6 -fno-tree-vectorize -flto
CCOPTS := -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops -DKRML_NOUINT128
CFLAGS= $(CCOPTS) -I $(OPENSSL_HOME) -I $(OPENSSL_HOME)/include -I $(OPENSSL_HOME)/crypto/ec \
	-I $(OPENSSL_HOME)/crypto/include -I $(OPENSSL_HOME)/crypto/poly1305 \
	-I $(LIBSODIUM_HOME)/include -L$(LIBSODIUM_HOME)/lib \
	-I $(TWEETNACL_HOME) -I . -I $(HACL_HOME)/snapshots/snapshot-ccomp -I $(HACL_HOME)/test/c/


perf: perf-test-poly32

test-poly32.exe: $(HACL_HOME)/test/c/hacl_test_utils.c $(TWEETNACL_HOME)/tweetnacl.c $(KREMLIN_HOME)/kremlib/kremlib.c $(KREMLIN_HOME)/kremlib/testlib.c FStar.c Poly1305_32.c test-poly32.c
	$(CC) $(CFLAGS) $^  -o test-poly32.exe -lsodium $(OPENSSL_HOME)/libcrypto.a

perf-test-poly32: test-poly32.exe
	./test-poly32.exe perf

unit-test-poly32: test-poly32.exe
	./test-poly32.exe unit-test

compcert-perf-test-poly32:
	$(MAKE) perf-test-poly32 CC=ccomp CCOPTS="-O3 -DKRML_NOUINT128 -DKRML_NOSTRUCT_PASSING -finline-asm -D_BSD_SOURCE -D_DEFAULT_SOURCE"

gcc-perf-test-poly32:
	$(MAKE) perf-test-poly32 CC=gcc-6 CCOPTS="-O3 -DKRML_NOUINT128 -DKRML_NOSTRUCT_PASSING -march=native -m64 -D_BSD_SOURCE -D_DEFAULT_SOURCE"

clean:
	rm -rf *.o *~ *.exe

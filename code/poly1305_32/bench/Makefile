include ../../Makefile.include

TWEETNACL_HOME?=../../../other_providers/tweetnacl
OPENSSL_HOME?=../../../other_providers/openssl
LIBSODIUM_HOME ?=../../../other_providers/libsodium/src/libsodium

CC?=gcc-6 -fno-tree-vectorize -flto
CCOPTS := -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops -DKRML_NOUINT128
CFLAGS= $(CCOPTS) -I $(OPENSSL_HOME) -I $(OPENSSL_HOME)/include -I $(OPENSSL_HOME)/crypto/ec \
	-I $(OPENSSL_HOME)/crypto/include -I $(OPENSSL_HOME)/crypto/poly1305 \
	-I $(LIBSODIUM_HOME)/include -L$(LIBSODIUM_HOME)/lib \
	-I $(TWEETNACL_HOME) -I . -I $(KREMLIN_HOME)/kremlib -I $(HACL_HOME)/test/c/


perf: perf-test-poly32

test-poly32.exe: $(HACL_HOME)/test/c/hacl_test_utils.c $(TWEETNACL_HOME)/tweetnacl.c $(KREMLIN_HOME)/kremlib/kremlib.c $(KREMLIN_HOME)/kremlib/testlib.c FStar.c Poly1305_32.c test-poly32.c
	$(CC) $(CFLAGS) $^  -o test-poly32.exe -lsodium $(OPENSSL_HOME)/libcrypto.a

perf-test-poly32: test-poly32.exe
	./test-poly32.exe perf

unit-test-poly32: test-poly32.exe
	./test-poly32.exe unit-test

clean:
	rm -rf *.o *~ *.exe

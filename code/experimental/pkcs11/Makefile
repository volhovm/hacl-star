include ../../Makefile.include

# Files that are too slow and for which verification speed must improve

FSTAR_INCLUDES+=--include ../bignum

PKCSFILES=\
	PKCS11.TypeDeclaration.fst\
	PKCS11.Cast.fst \
	PKCS11.TypeDeclaration.fst \
	PKCS11.Attribute.fst \
	PKCS11.Pointer.fst \
	PKCS11.Mechanism.fst\
	PKCS11.Exception.fst \
	PKCS11.Parse.fst \
	PKCS11.Objects.fst\
	PKCS11.Test.fst




KREMLIN_ARGS+= -tmpdir pkcs \
	-drop Spec.*,Hacl.Spec.*,Hacl.Cast,Hacl.UInt.*,Hacl.Endianness,Hacl.UInt8,Hacl.UInt16,Hacl.UInt32,Hacl.UInt64,Hacl.UInt128,Prims \

build: $(PKCSFILES)
	$(KREMLIN) $(KREMLIN_ARGS) -no-prefix 'PKCS11.Test' -no-prefix 'PKCS11.Test' -no-prefix 'PKCS11.Parse' -no-prefix 'PKCS11.Exception' -no-prefix 'PKCS11.Mechanism' -no-prefix 'PKCS11.Pointer' -no-prefix 'PKCS11.Attribute' -no-prefix 'PKCS11.TypeDeclaration' -no-prefix 'PKCS11.Cast' -no-prefix 'PKCS11.TypeDeclaration' -skip-compilation $^ -o $@

buildWithUniv: $(PKCSFILES)
	$(KREMLIN) $(KREMLIN_ARGS)  -skip-compilation $^ -o $@



buildrun: $(PKCSFILES)
	$(KREMLIN) $(KREMLIN_ARGS) -no-prefix 'FStar.PKCS11.Attribute' -no-prefix 'FStar.Pervasives.either'  -no-prefix 'FStar.PKCS11.Exception'  -no-prefix 'FStar.PKCS11.TypeDeclaration'  -no-prefix 'FStar.PKCS11.Exception' -no-prefix 'FStar.PKCS11.DateTime' -no-prefix 'FStar.PKCS11.Mechanism' -no-prefix 'PKCS11.Test'   $^ -o $@

module FStar.PKCS11.Session

open FStar.Seq

type session = |Session: id1: FStar.UInt32.t -> id2: seq Fstar.UInt8 -> session
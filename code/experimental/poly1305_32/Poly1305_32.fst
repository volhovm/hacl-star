module Poly1305_32

open FStar.HyperStack.All

module ST = FStar.HyperStack.ST

open FStar.Mul
open FStar.HyperStack.ST
open FStar.Ghost
open FStar.Seq
open FStar.Buffer
open FStar.HyperStack

open Hacl.Cast
open Hacl.MAC.Poly1305_32

module H8   = Hacl.UInt8
module Limb = Hacl.Bignum.Limb
module Wide = Hacl.Bignum.Wide
module U8   = FStar.UInt8
module U32  = FStar.UInt32
module U64  = FStar.UInt64

let crypto_onetimeauth output input len k = crypto_onetimeauth output input len k

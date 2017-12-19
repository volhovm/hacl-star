module Hacl.P256.Contract

open FStar.Mul

open FStar.HyperStack
open FStar.HyperStack.ST

open Spec.Lib
open Spec.Lib.IntSeq

open Spec.Lib.IntTypes
open Spec.Lib.IntBuf

open Spec.Lib.IntSeq.Lemmas
open Spec.Lib.IntBuf.Lemmas

open P256.S
open Hacl.P256.Zeros
open Hacl.P256.Shrink

open FStar.Math.Lemmas

val subtract_u64:
  result:uint64 -> v:uint64 -> Tot (tuple2 uint64 uint64)

let subtract_u64 result v' =
  let r = to_u128 result in
  let r = to_u128(r -! to_u128 v') in  
  let carry = to_u64(to_u64 (r >>. u32(64))) &. u64(1) in
  let result = to_u64 r in
  result, carry

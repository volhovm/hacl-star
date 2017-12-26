module Hacl.P256.IsZero

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

val smallfelem_is_zero:
  small:smallfelem -> Stack limb
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))

let smallfelem_is_zero small =
	alloc  #(uint_t U64) #(limb) #(v(size 4)) (size 4) (u64(0)) [BufItem small] [] 
		(fun h0 _ h1 -> True) (
			fun kPrime -> 
  kPrime_ kPrime;
  let kPrime0 = kPrime.(size 0) in
  let kPrime1 = kPrime.(size 1) in
  let kPrime2 = kPrime.(size 2) in
  let kPrime3 = kPrime.(size 3) in
  let small0 = small.(size 0) in
  let small1 = small.(size 1) in
  let small2 = small.(size 2) in
  let small3 = small.(size 3) in
  let is_zero = to_u64(small0 |. small1 |. small2 |. small3) in
  let is_zero = eq_mask is_zero (u64(0)) in
  let is_p = (small0 ^. kPrime0) |. (small1 ^. kPrime1) |. (small2 ^. kPrime2) |. (small3 ^. kPrime3) in
  let is_p = eq_mask is_p (u64(0)) in
  let is_zero = is_zero |. is_p in
  let result = (to_u128 is_zero |. (to_u128 is_zero <<. u32(64))) in
  result
)

val smallfelem_is_zero_int:
  small:smallfelem -> Stack (uint_t U32)
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))

let smallfelem_is_zero_int small =
  let w = smallfelem_is_zero small in
  (to_u32 (to_u64 (w &. (u128 (1)))))

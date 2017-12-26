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
open Hacl.P256.Mult
open Hacl.P256.Reduce

open FStar.Math.Lemmas

val subtract_u64:
  result:uint64 -> v:uint64 -> Tot (tuple2 uint64 uint64)

let subtract_u64 result v' =
  let r = to_u128 result in
  let r = to_u128(r -! to_u128 v') in  
  let carry = to_u64(to_u64 (r >>. u32(64))) &. u64(1) in
  let result = to_u64 r in
  result, carry

val felem_contract:
  out:smallfelem -> input:felem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))

let felem_contract out input =
	alloc   #(uint_t U64) #(unit) #(v(size 4)) (size 4) (u64(0)) [BufItem input] [BufItem out] 
		(fun h0 _ h1 -> True) (
			fun kPrime -> 
  let all_equal_so_far = u64(0) in
  let result = u64(0) in
  felem_shrink out input;
  let all_equal_so_far =
  		to_u64(all_equal_so_far -. (u64(1))) in
  kPrime_ kPrime;
  let kPrime0 = kPrime.(size 0) in
  let kPrime1 = kPrime.(size 1) in
  let kPrime2 = kPrime.(size 2) in
  let kPrime3 = kPrime.(size 3) in
  let out0 = out.(size 0) in
  let out1 = out.(size 1) in
  let out2 = out.(size 2) in
  let out3 = out.(size 3) in
  let a = to_u128 kPrime0 -! to_u128 out0 in
  let result = to_u64 (result |. (all_equal_so_far &. (to_u64 (a >>. u32(64))))) in

  let equal = kPrime3 ^. out3 in
  let equal = equal -! (u64(1)) in
  let equal = equal &. (equal <<. u32(32)) in
  let equal = equal &. (equal <<. u32(16)) in
  let equal = equal &. (equal <<. u32(8)) in
  let equal = equal &. (equal <<. u32(4)) in
  let equal = equal &. (equal <<. u32(2)) in
  let equal = equal &. (equal <<. u32(1)) in
  let equal = gte_mask equal (u64(0x1000000000000000)) in
  let all_equal_so_far = all_equal_so_far &. equal in


  let equal = kPrime2 ^. out2 in
  let equal = equal -! (u64(1)) in
  let equal = equal &. (equal <<. u32(32)) in
  let equal = equal &. (equal <<. u32(16)) in
  let equal = equal &. (equal <<. u32(8)) in
  let equal = equal &. (equal <<. u32(4)) in
  let equal = equal &. (equal <<. u32(2)) in
  let equal = equal &. (equal <<. u32(1)) in
  let equal = gte_mask equal (u64(0x1000000000000000)) in
  let all_equal_so_far = all_equal_so_far &. equal in

  let equal = kPrime1 ^. out1 in
  let equal = equal -! (u64(1)) in
  let equal = equal &. (equal <<. u32(32)) in
  let equal = equal &. (equal <<. u32(16)) in
  let equal = equal &. (equal <<. u32(8)) in
  let equal = equal &. (equal <<. u32(4)) in
  let equal = equal &. (equal <<. u32(2)) in
  let equal = equal &. (equal <<. u32(1)) in
  let equal = gte_mask equal (u64(0x1000000000000000)) in
  let all_equal_so_far = all_equal_so_far &. equal in

  let equal = kPrime0 ^. out0 in
  let equal = equal -! (u64(1)) in
  let equal = equal &. (equal <<. u32(32)) in
  let equal = equal &. (equal <<. u32(16)) in
  let equal = equal &. (equal <<. u32(8)) in
  let equal = equal &. (equal <<. u32(4)) in
  let equal = equal &. (equal <<. u32(2)) in
  let equal = equal &. (equal <<. u32(1)) in
  let equal = gte_mask equal (u64(0x1000000000000000)) in
  let all_equal_so_far = all_equal_so_far &. equal in

  let result = result |. all_equal_so_far in

  let out0, carry = subtract_u64 out0 (result &. kPrime0) in
  let out1, carry = subtract_u64 out1 carry in
  let out2, carry = subtract_u64 out2 carry in
  let out3, carry = subtract_u64 out3 carry in

  let out1, carry = subtract_u64 out1 (result &. kPrime1) in
  let out2, carry = subtract_u64 out2 carry in
  let out3, carry = subtract_u64 out3 carry in

  let out2, carry = subtract_u64 out2 (result &. kPrime2) in
  let out3, carry = subtract_u64 out3 carry in

  let out3, carry = subtract_u64 out3 (result &. kPrime3) in ()
)

val smallfelem_mul_contract:
  out:smallfelem -> in1:smallfelem -> in2:smallfelem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))

let smallfelem_mul_contract out in1 in2 =
	alloc  #(uint_t U128) #(unit) #(v(size 12)) (size 12) (u128(0)) [BufItem in1; BufItem in2] [BufItem out] 
		(fun h0 _ h1 -> True) (
			fun temp -> 
  let longtmp = sub temp (size 0) (size 8) in
  let tmp     = sub temp (size 8) (size 4) in
  smallfelem_mul longtmp in1 in2;
  felem_reduce tmp longtmp;
  felem_contract out tmp
)
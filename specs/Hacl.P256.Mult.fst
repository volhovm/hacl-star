module Hacl.P256.Mult

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


val smallfelem_mul:
  out:longfelem -> small1:smallfelem -> small2:smallfelem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))

let smallfelem_mul out small1 small2 =
  let small10 = small1.(size 0) in
  let small11 = small1.(size 1) in
  let small12 = small1.(size 2) in
  let small13 = small1.(size 3) in
  let small20 = small2.(size 0) in
  let small21 = small2.(size 1) in
  let small22 = small2.(size 2) in
  let small23 = small2.(size 3) in

  let a = mul_wide small10 small20 in
  let low = to_u128 (to_u64 a) in
  let high = a >>.  u32(64) in
  let out0 = low in
  let out1 = high in

  let a = mul_wide small10 small21 in
  let low = to_u128 (to_u64 a) in
  let high = a >>. u32(64) in
  let out1 = out1 +! low in
  let out2 = high in

  let a = mul_wide small11 small20 in
  let low = to_u128 (to_u64 a) in
  let high = a >>. u32(64) in
  let out1 = out1 +! low in
  let out2 = out2 +! high in

  let a = mul_wide small10 small22 in
  let low = to_u128 (to_u64 a) in
  let high = a >>. u32(64) in
  let out2 = out2 +! low in
  let out3 = high in

  let a = mul_wide small11 small21 in
  let low = to_u128 (to_u64 a) in
  let high = a >>. u32(64) in
  let out2 = out2 +! low in
  let out3 = out3 +! high in

  let a = mul_wide small12 small20 in
  let low = to_u128 (to_u64 a) in
  let high = a >>. u32(64) in
  let out2 = out2 +! low in
  let out3 = out3 +! high in

  let a = mul_wide small10 small23 in
  let low = to_u128 (to_u64 a) in
  let high = a >>. u32(64) in
  let out3 = out3 +! low in
  let out4 = high in

  let a = mul_wide small11 small22 in
  let low = to_u128 (to_u64 a) in
  let high = a >>. u32(64) in
  let out3 = out3 +! low in
  let out4 = out4 +! high in

  let a = mul_wide small12 small21 in
  let low = to_u128 (to_u64 a) in
  let high = a >>. u32(64) in
  let out3 = out3 +! low in
  let out4 = out4 +! high in

  let a = mul_wide small13 small20 in
  let low = to_u128 (to_u64 a) in
  let high = a >>. u32(64) in
  let out3 = out3 +! low in
  let out4 = out4 +! high in

  let a = mul_wide small11 small23 in
  let low = to_u128 (to_u64 a) in
  let high = a >>. u32(64) in
  let out4 = out4 +! low in
  let out5 = high in

  let a = mul_wide small12 small22 in
  let low = to_u128 (to_u64 a) in
  let high = a >>. u32(64) in
  let out4 = out4 +! low in
  let out5 = out5 +! high in

  let a = mul_wide small13 small21 in
  let low = to_u128 (to_u64 a) in
  let high = a >>. u32(64) in
  let out4 = out4 +! low in
  let out5 = out5 +! high in

  let a = mul_wide small12 small23 in
  let low = to_u128 (to_u64 a) in
  let high = a >>. u32(64) in
  let out5 = out5 +! low in
  let out6 = high in

  let a = mul_wide small13 small22 in
  let low = to_u128 (to_u64 a) in
  let high = a >>. u32(64) in
  let out5 = out5 +! low in
  let out6 = out6 +! high in

  let a = mul_wide small13 small23 in
  let low = to_u128 (to_u64 a) in
  let high = a >>. u32(64) in
  let out6 = out6 +! low in
  let out7 = high in

  out.(size 0) <- out0;
  out.(size 1) <- out1;
  out.(size 2) <- out2;
  out.(size 3) <- out3;
  out.(size 4) <- out4;
  out.(size 5) <- out5;
  out.(size 6) <- out6;
  out.(size 7) <- out7


val felem_mul:
  out:longfelem -> in1:felem -> in2:felem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))

let felem_mul out in1 in2 =
	alloc #(uint_t U64) #(unit) #(v(size 8)) (size 8) (u64(0)) [BufItem in1; BufItem in2] [BufItem out] 
		(fun h0 _ h1 -> True) (
			fun tmp -> 
  let small1 = sub tmp (size 0) (size 4) in 
  let small2 = sub tmp (size 4) (size 4) in 
  felem_shrink small1 in1;
  felem_shrink small2 in2;
  smallfelem_mul out small1 small2
)

val felem_small_mul:
  out:longfelem -> small1:smallfelem -> in2:felem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))

let felem_small_mul out small1 in2 =
  	alloc #(uint_t U64) #(unit) #(v(size 4)) (size 4) (u64(0)) [BufItem small1; BufItem in2] [BufItem out] 
		(fun h0 _ h1 -> True) (
			fun tmp -> 
	let small2 = sub tmp (size 0) (size 4) in 		
	felem_shrink small2 in2;
	smallfelem_mul out small1 small2
)
	
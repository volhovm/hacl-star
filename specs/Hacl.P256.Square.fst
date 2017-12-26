module Hacl.P256.Square

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

val smallfelem_expand:
  out:felem -> input:smallfelem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))

let smallfelem_expand out input =
  let input0 = input.(size 0) in
  let input1 = input.(size 1) in
  let input2 = input.(size 2) in
  let input3 = input.(size 3) in
  out.(size 0) <- to_u128 input0;
  out.(size 1) <- to_u128 input1;
  out.(size 2) <- to_u128 input2;
  out.(size 3) <- to_u128 input3

val smallfelem_square:
  out:longfelem -> small:smallfelem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))

let smallfelem_square out small =
  let small0 = small.(size 0) in
  let small1 = small.(size 1) in
  let small2 = small.(size 2) in
  let small3 = small.(size 3) in

  let a = mul_wide small0 small0 in
  let low = to_u128 (to_u64 a) in
  let high = a >>. u32(64) in
  let out0 = low in
  let out1 = high in

  let a = mul_wide small0 small1 in
  let low = to_u128 (to_u64 a) in
  let high = a >>. u32(64) in
  let out1 = out1 +! low in
  let out1 = out1 +! low in
  let out2 = high in

  let a = mul_wide small0 small2 in
  let low = to_u128 (to_u64 a) in
  let high = a >>. u32(64) in
  let out2 = out2 +! low in
  let out2 = out2 <<. u32(1) in
  let out3 = high in

  let a = mul_wide small0 small3 in
  let low = to_u128 (to_u64 a) in
  let high = a >>. u32(64) in
  let out3 = out3 +! low in
  let out4 = high in

  let a = mul_wide small1 small2 in
  let low = to_u128 (to_u64 a) in
  let high = a >>. u32(64) in
  let out3 = out3 +! low in
  let out3 = out3 <<. u32(1) in
  let out4 = out4 +! high in

  let a = mul_wide small1 small1 in
  let low = to_u128 (to_u64 a) in
  let high = a >>. u32(64) in
  let out2 = out2 +! low in
  let out3 = out3 +! high in

  let a = mul_wide small1 small3 in
  let low = to_u128 (to_u64 a) in
  let high = a >>. u32(64) in
  let out4 = out4 +! low in
  let out4 = out4 <<. u32(1) in
  let out5 = high in

  let a = mul_wide small2 small3 in
  let low = to_u128 (to_u64 a) in
  let high = a >>. u32(64) in
  let out5 = out5 +! low in
  let out5 = out5 <<. u32(1) in
  let out6 = high in
  let out6 = out6 +! high in

  let a = mul_wide small2 small2 in
  let low = to_u128 (to_u64 a) in
  let high = a >>. u32(64) in
  let out4 = out4 +! low in
  let out5 = out5 +! high in

  let a = mul_wide small3 small3 in
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

val felem_square:
  out:longfelem -> input:felem ->  Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))

let felem_square out input =
    alloc  #(uint_t U64) #(unit) #(v(size 4)) (size 4) (u64(0)) [BufItem input] [BufItem out] 
    (fun h0 _ h1 -> True) (
      fun small ->
  felem_shrink small input;
  smallfelem_square out small
)

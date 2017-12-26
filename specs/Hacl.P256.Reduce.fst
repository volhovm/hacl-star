module Hacl.P256.Reduce

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


val felem_reduce_:
  out:felem -> input:longfelem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))

let felem_reduce_ out input =
  let out0 = out.(size 0) in
  let out1 = out.(size 1) in
  let out2 = out.(size 2) in
  let out3 = out.(size 3) in
  let input0 = input.(size 0) in
  let input1 = input.(size 1) in
  let input2 = input.(size 2) in
  let input3 = input.(size 3) in
  let input4 = input.(size 4) in
  let input5 = input.(size 5) in
  let input6 = input.(size 6) in
  let input7 = input.(size 7) in
  let c = input4 +! (input5 <<. u32(32)) in
  let out0 = out0 +! c in
  let out3 = out3 -! c in
  let out1 = out1 +! input5 -! input7 in
  let out2 = out2 +! input7 -! input5 in
  let out1 = out1 -! (input4 <<. u32(32)) in
  let out3 = out3 +! (input4 <<. u32(32)) in
  let out2 = out2 -! (input5 <<. u32(32)) in
  let out0 = out0 -! input6 in
  let out0 = out0 -! (input6 <<. u32(32)) in
  let out1 = out1 +! (input6 <<. u32(33)) in
  let out2 = out2 +! (input6 <<. u32(1))  in
  let out3 = out3 -! (input6 <<. u32(32)) in
  let out0 = out0 -! input7 in
  let out0 = out0 -! (input7 <<. u32(32)) in
  let out2 = out2 +! (input7 <<. u32(33)) in
  let out3 = out3 +! ((input7 <<. u32(1)) +! input7) in
  out.(size 0) <- out0;
  out.(size 1) <- out1;
  out.(size 2) <- out2;
  out.(size 3) <- out3

val felem_reduce:
  out:felem -> input:longfelem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))

let felem_reduce out input =
	alloc #(uint_t U128) #(unit) #(v(size 4)) (size 4) (u128(0)) [BufItem input] [BufItem out] 
		(fun h0 _ h1 -> True) (
			fun tmp -> 
  let zero100 = zero100() in
  let zero0 = zero100.(size 0) in
  let zero1 = zero100.(size 1) in
  let zero2 = zero100.(size 2) in
  let zero3 = zero100.(size 3) in
  let input0 = input.(size 0) in
  let input1 = input.(size 1) in
  let input2 = input.(size 2) in
  let input3 = input.(size 3) in
  out.(size 0) <- input0 +! zero0;
  out.(size 1) <- input1 +! zero1;
  out.(size 2) <- input2 +! zero2;
  out.(size 3) <- input3 +! zero3;
  felem_reduce_ out input
)

val felem_reduce_zero105:
  out:felem -> input:longfelem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))

let felem_reduce_zero105 out input =
	alloc #(uint_t U128) #(unit) #(v(size 4)) (size 4) (u128(0)) [BufItem input] [BufItem out] 
		(fun h0 _ h1 -> True) (
			fun tmp -> 
  let zero105 = zero105() in
  let zero0 = zero105.(size 0) in
  let zero1 = zero105.(size 1) in
  let zero2 = zero105.(size 2) in
  let zero3 = zero105.(size 3) in
  let input0 = input.(size 0) in
  let input1 = input.(size 1) in
  let input2 = input.(size 2) in
  let input3 = input.(size 3) in
  out.(size 0) <- input0 +! zero0;
  out.(size 1) <- input1 +! zero1;
  out.(size 2) <- input2 +! zero2;
  out.(size 3) <- input3 +! zero3;
  felem_reduce_ out input
)
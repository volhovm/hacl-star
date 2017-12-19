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
  let out0 = out.(0) in
  let out1 = out.(1) in
  let out2 = out.(2) in
  let out3 = out.(3) in
  let input0 = input.(0) in
  let input1 = input.(1) in
  let input2 = input.(2) in
  let input3 = input.(3) in
  let input4 = input.(4) in
  let input5 = input.(5) in
  let input6 = input.(6) in
  let input7 = input.(7) in
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
  out.(0) <- out0;
  out.(1) <- out1;
  out.(2) <- out2;
  out.(3) <- out3

val felem_reduce:
  out:felem -> input:longfelem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))

let felem_reduce out input =
	alloc 4 (u128(0)) [BufItem input] [BufItem out] 
		(fun h0 _ h1 -> True) (
			fun tmp -> 
  let zero100 = zero100() in
  let zero0 = zero100.(0) in
  let zero1 = zero100.(1) in
  let zero2 = zero100.(2) in
  let zero3 = zero100.(3) in
  let input0 = input.(0) in
  let input1 = input.(1) in
  let input2 = input.(2) in
  let input3 = input.(3) in
  out.(0) <- input0 +! zero0;
  out.(1) <- input1 +! zero1;
  out.(2) <- input2 +! zero2;
  out.(3) <- input3 +! zero3;
  felem_reduce_ out input
)

val felem_reduce_zero105:
  out:felem -> input:longfelem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))

let felem_reduce_zero105 out input =
	alloc 4 (u128(0)) [BufItem input] [BufItem out] 
		(fun h0 _ h1 -> True) (
			fun tmp -> 
  let zero105 = zero105() in
  let zero0 = zero105.(0) in
  let zero1 = zero105.(1) in
  let zero2 = zero105.(2) in
  let zero3 = zero105.(3) in
  let input0 = input.(0) in
  let input1 = input.(1) in
  let input2 = input.(2) in
  let input3 = input.(3) in
  out.(0) <- input0 +! zero0;
  out.(1) <- input1 +! zero1;
  out.(2) <- input2 +! zero2;
  out.(3) <- input3 +! zero3;
  felem_reduce_ out input
)
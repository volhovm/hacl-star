module Hacl.P256.Inv

open FStar.Mul

open FStar.HyperStack
open FStar.HyperStack.ST

open Spec.Lib
open Spec.Lib.IntSeq

open Spec.Lib.IntTypes
open Spec.Lib.IntBuf
open Spec.Lib.Loops


//open Spec.Lib.IntSeq.Lemmas
open Spec.Lib.IntBuf.Lemmas

open P256.S
open Hacl.P256.Zeros
open Hacl.P256.Shrink

open Hacl.P256.Mult
open Hacl.P256.Reduce
open Hacl.P256.Square

val felem_inv:
  out:felem -> input:felem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))

let felem_inv out input =
    alloc 40 (u128(0)) [BufItem input] [BufItem out] 
    (fun h0 _ h1 -> True) (
      fun tmp ->
  let ftmp = sub tmp 0 4 in
  let ftmp2 =  sub tmp 4 4 in
  let e2 =  sub tmp 8 4 in
  let e4 = sub tmp 12 4 in
  let e8 =  sub tmp 16 4 in
  let e16 =  sub tmp 20 4 in
  let e32 =  sub tmp 24 4 in
  let e64 =  sub tmp 28 4 in
  let tmp =  sub tmp 32 4 in
  felem_square tmp input;
  felem_reduce ftmp tmp;
  felem_mul tmp input ftmp;
  felem_reduce ftmp tmp;
  felem_assign e2 ftmp;
  felem_square tmp ftmp;
  felem_reduce ftmp tmp;
  felem_square tmp ftmp;
  felem_reduce ftmp tmp;
  felem_mul tmp ftmp e2;
  felem_reduce ftmp tmp;
  felem_assign e4 ftmp;
  felem_square tmp ftmp;
  felem_reduce ftmp tmp;
  felem_square tmp ftmp;
  felem_reduce ftmp tmp;
  felem_square tmp ftmp;
  felem_reduce ftmp tmp;
  felem_square tmp ftmp;
  felem_reduce ftmp tmp;
  felem_mul tmp ftmp e4;
  felem_reduce ftmp tmp;
  felem_assign e8 ftmp;
    let inv (h1:mem) (i:nat) = True in
    let f (i:uint_t U32) : Stack unit
      (requires (fun h -> True))
      (ensures (fun h0 _ h1 -> True))
      = felem_square tmp ftmp;
        felem_reduce ftmp tmp in
    let f' (i: uint_t U32) : Stack unit
      (requires (fun h -> True))
      (ensures (fun h0 _ h1 -> True))
      = felem_square tmp ftmp2;
        felem_reduce ftmp2 tmp in
  
  for 0 8 inv f
    ) (*); 
          
  //for 0 8 inv f;
  felem_mul tmp ftmp e8;
  felem_reduce ftmp tmp;
  felem_assign e16 ftmp;
  for 0 16 inv f;
  felem_mul tmp ftmp e16;
  felem_reduce ftmp tmp;
  felem_assign e32 ftmp;
  for 0 32 inv f;
  felem_assign e64 ftmp;
  felem_mul tmp ftmp input;
  felem_reduce ftmp tmp;
  for 0 192 inv f;
  felem_mul tmp e64 e32;
  felem_reduce ftmp2 tmp;
  for 0 16 inv f';
  felem_mul tmp ftmp2 e16;
  felem_reduce ftmp2 tmp;
  for 0 8 inv f';
  felem_mul tmp ftmp2 e8;
  felem_reduce ftmp2 tmp;
  for 0 4 inv f';
  felem_mul tmp ftmp2 e4;
  felem_reduce ftmp2 tmp;
  felem_square tmp ftmp2;
  felem_reduce ftmp2 tmp;
  felem_square tmp ftmp2;
  felem_reduce ftmp2 tmp;
  felem_mul tmp ftmp2 e2;
  felem_reduce ftmp2 tmp;
  felem_square tmp ftmp2;
  felem_reduce ftmp2 tmp;
  felem_square tmp ftmp2;
  felem_reduce ftmp2 tmp;
  felem_mul tmp ftmp2 input;
  felem_reduce ftmp2 tmp;

  felem_mul tmp ftmp2 ftmp;
  felem_reduce out tmp
)


val smallfelem_inv_contract:
  out:smallfelem -> input:smallfelem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let smallfelem_inv_contract out input =
  push_frame();
  let tmp = create (UInt128.uint64_to_uint128 0uL) 4ul in
  smallfelem_expand tmp input;
  felem_inv tmp tmp;
  felem_contract out tmp;
  pop_frame()
module Hacl.P256.Inv

open FStar.Mul

open FStar.HyperStack
open FStar.HyperStack.ST

open Spec.Lib.Loops

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
open Hacl.P256.Square
open Hacl.P256.Contract

val felem_inv:
  out:felem -> input:felem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))

let felem_inv out input =
    alloc  #(uint_t U128) #(unit) #(v(size 40)) (size 40) (u128(0)) [BufItem input] [BufItem out] 
    (fun h0 _ h1 -> True) (
      fun tmp ->
  let ftmp = sub tmp (size 0) (size 4) in
  let ftmp2 =  sub tmp (size 4) (size 4) in
  let e2 =  sub tmp (size 8) (size 4) in
  let e4 = sub tmp (size 12) (size 4) in
  let e8 =  sub tmp (size 16) (size 4) in
  let e16 =  sub #_ #_ #(v(size 4)) tmp (size 20) (size 4) in
  let e32 =  sub #_ #_ #(v(size 4)) tmp (size 24) (size 4) in
  let e64 =  sub #_ #_ #(v(size 4)) tmp (size 28) (size 4) in
  let tmp =  sub #_ #_ #(v(size 8)) tmp (size 32) (size 8) in
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
    let f (i:size_t) : Stack unit
      (requires (fun h -> True))
      (ensures (fun h0 _ h1 -> True))
      = felem_square tmp ftmp;
        felem_reduce ftmp tmp in
    let f' (i: size_t) : Stack unit
      (requires (fun h -> True))
      (ensures (fun h0 _ h1 -> True))
      = felem_square tmp ftmp2;
        felem_reduce ftmp2 tmp in
  
  for (size 0) (size 8) inv f;
  felem_mul tmp ftmp e8;
  felem_reduce ftmp tmp;
  felem_assign e16 ftmp;
  for (size 0) (size 16) inv f;
  felem_mul tmp ftmp e16;
  felem_reduce ftmp tmp;
  felem_assign e32 ftmp;
  for (size 0) (size 32) inv f;
  felem_assign e64 ftmp;
  felem_mul tmp ftmp input;
  felem_reduce ftmp tmp;
  for (size 0) (size 192) inv f;
  felem_mul tmp e64 e32;
  felem_reduce ftmp2 tmp;
  for (size 0) (size 16) inv f';
  felem_mul tmp ftmp2 e16;
  felem_reduce ftmp2 tmp;
  for (size 0) (size 8) inv f';
  felem_mul tmp ftmp2 e8;
  felem_reduce ftmp2 tmp;
  for (size 0) (size 4) inv f';
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
  alloc  #(uint_t U128) #(unit) #(v(size 4)) (size 4) (u128(0)) 
        [BufItem input] [BufItem out] 
    (fun h0 _ h1 -> True) (
      fun tmp ->
  //let tmp = create (UInt128.uint64_to_uint128 0uL) 4ul in
  smallfelem_expand tmp input;
  felem_inv tmp tmp;
  felem_contract out tmp
)
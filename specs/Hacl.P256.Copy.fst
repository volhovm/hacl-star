module Hacl.P256.Copy

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
open Hacl.P256.SmallNegation


val copy_conditional:
  out:felem -> input:felem -> mask:limb -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))

let copy_conditional out input mask =
  let inv (h1:mem) (i:nat) = True in
  let f (i:size_t) : Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
    = let inputi = input.(i) in
      let outi = out.(i) in
      let tmp = mask &. (inputi ^. outi) in
      out.(i) <- outi ^. tmp in
  for (size 0) (size 4) inv f

val copy_small_conditional:
  out:felem -> input:smallfelem -> mask:limb -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))

let copy_small_conditional out input mask =
  let mask64 = to_u64(mask) in
  let inv (h1:mem) (i:nat) = True in
  let f (i:size_t) : Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
    = let inputi = input.(i) in
      let outi = out.(i) in
      let tmp = to_u128 (to_u64(inputi &. mask64)) |. (outi &. lognot mask) in
      out.(i) <- tmp in
  for (size 0) (size 4) inv f

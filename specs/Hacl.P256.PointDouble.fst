module Hacl.P256.PointDouble

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

val point_double:
  x_out:felem -> y_out:felem -> z_out:felem ->
  x_in:felem -> y_in:felem -> z_in:felem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))

let point_double x_out y_out z_out x_in y_in z_in =
	alloc  #(uint_t U128) #(unit) #(v(size 44)) (size 44) (u128(0)) 
		[BufItem x_in; BufItem y_in; BufItem z_in] [BufItem x_out; BufItem y_out; BufItem z_out] 
    (fun h0 _ h1 -> True) (
      fun temp ->
 		let tmp = sub #_ #_ #(v(size 8)) temp (size 0) (size 8) in 
 		let tmp2 = sub #_ #_ #(v(size 8)) temp (size 8) (size 8) in 
 		let delta = sub #_ #_ #(v(size 4)) temp (size 16) (size 4) in 
 		let gamma = sub #_ #_ #(v(size 4)) temp (size 20) (size 4) in 
 		let beta = sub #_ #_ #(v(size 4)) temp (size 24) (size 4) in 
 		let alpha = sub #_ #_ #(v(size 4)) temp (size 28) (size 4) in 
 		let ftmp = sub #_ #_ #(v(size 4)) temp (size 32) (size 4) in 
 		let ftmp2 = sub #_ #_ #(v(size 4)) temp (size 36) (size 4) in 
 		let tempHacl = sub #_ #_ #(v(size 4)) temp (size 40) (size 4) in 

  let small1 = create (size 4) (u64 0) in
  let small2 = create (size 4) (u64 4) in

  felem_assign ftmp x_in;
  felem_assign ftmp2 x_in;

  felem_square tmp z_in;
  felem_reduce delta tmp;

  felem_square tmp y_in;
  felem_reduce gamma tmp;
  felem_shrink small1 gamma;

  felem_small_mul tmp small1 x_in;
  felem_reduce beta tmp;

  felem_diff ftmp delta;
  felem_sum ftmp2 delta;

  // TODO: check correctness
  // NB: I've introduces a new variable:
  felem_assign tempHacl ftmp2;
  felem_scalar ftmp2 (u32 1);
  felem_sum ftmp2 tempHacl;
  // END TODO

  felem_mul tmp ftmp ftmp2;
  felem_reduce alpha tmp;
  felem_shrink small2 alpha;

  smallfelem_square tmp small2;
  felem_reduce x_out tmp;
  felem_assign ftmp beta;
  felem_scalar ftmp (u32 3);
  felem_diff x_out ftmp;

  felem_sum delta gamma;
  felem_assign ftmp y_in;
  felem_sum ftmp z_in;
  felem_square tmp ftmp;
  felem_reduce z_out tmp;
  felem_diff z_out delta;

  felem_scalar beta (u32 2);
  felem_diff_zero107 beta x_out;
  felem_small_mul tmp small2 beta;
  smallfelem_square tmp2 small1;
  longfelem_scalar tmp2 (u64 3);
  longfelem_diff tmp tmp2;
  felem_reduce_zero105 y_out tmp
)
  

val point_double_small:
  x_out:smallfelem -> y_out:smallfelem -> z_out:smallfelem ->
  x_in:smallfelem -> y_in:smallfelem -> z_in:smallfelem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))

let point_double_small x_out y_out z_out x_in y_in z_in =
	alloc  #(uint_t U128) #(unit) #(v(size 24)) (size 24) (u128(0)) 
		[BufItem x_in; BufItem y_in; BufItem z_in] [BufItem x_out; BufItem y_out; BufItem z_out] 
    (fun h0 _ h1 -> True) (
      fun temp ->
		let felem_x_out = sub temp (size 0) (size 4) in
		let felem_y_out = sub temp (size 4) (size 4) in
		let felem_z_out = sub temp (size 8) (size 4) in
		let felem_x_in = sub temp (size 12) (size 4) in
		let felem_y_in = sub temp (size 16) (size 4) in
		let felem_z_in = sub temp (size 20) (size 4) in
  point_double felem_x_out felem_y_out felem_z_out felem_x_in felem_y_in felem_z_in;
  felem_shrink x_out felem_x_out;
  felem_shrink y_out felem_y_out;
  felem_shrink z_out felem_z_out
)
module Hacl.P256.PointAdd

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
open Hacl.P256.IsZero
open Hacl.P256.PointDouble
open Hacl.P256.Copy

val point_add:
  x3:felem -> y3:felem -> z3:felem ->
  x1:felem -> y1:felem -> z1:felem ->
  mixed:(uint_t U32) -> 
  x2:smallfelem -> y2:smallfelem -> z2:smallfelem ->
  Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))

let point_add x3 y3 z3 x1 y1 z1 mixed x2 y2 z2 =
	alloc  #(uint_t U128) #(unit) #(v(size 52)) (size 52) (u128(0)) 
		[BufItem x1; BufItem y1; BufItem z1;
			BufItem x2; BufItem y2; BufItem z2] 
		[BufItem x3; BufItem y3; BufItem z3] 
    (fun h0 _ h1 -> True) (
      fun temp ->
  let ftmp =  sub temp (size 0) (size 4) in
  let ftmp2 = sub temp (size 4) (size 4) in
  let ftmp3 = sub temp (size 8) (size 4) in
  let ftmp4 =  sub temp (size 12) (size 4) in
  let ftmp5 =  sub temp (size 16) (size 4) in
  let ftmp6 =  sub temp (size 20) (size 4) in
  let x_out =  sub temp (size 24) (size 4) in
  let y_out =  sub temp (size 28) (size 4) in
  let z_out =  sub temp (size 32) (size 4) in
  let tmp   =  sub temp (size 36) (size 8) in 
  let tmp2   = sub temp (size 44) (size 8) in 
  let small1 = create_smallfelem() in
  let small2 = create_smallfelem() in
  let small3 = create_smallfelem() in
  let small4 = create_smallfelem() in
  let small5 = create_smallfelem() in

  felem_shrink small3 z1;

  let z1_is_zero = smallfelem_is_zero small3 in
  let z2_is_zero = smallfelem_is_zero z2 in

  smallfelem_square tmp small3;
  felem_reduce ftmp tmp;
  felem_shrink small1 ftmp;

  if (mixed = u32(0)) then
    begin
      smallfelem_square tmp z2;
      felem_reduce ftmp2 tmp;
      felem_shrink small2 ftmp2;

      felem_shrink small5 x1;

      smallfelem_mul tmp small5 small2;
      felem_reduce ftmp3 tmp;

      felem_assign ftmp5 z1;
      felem_small_sum ftmp5 z2;

      felem_square tmp ftmp5;
      felem_reduce ftmp5 tmp;
      felem_sum ftmp2 ftmp;
      felem_diff ftmp5 ftmp2;

      smallfelem_mul tmp small2 z2;
      felem_reduce ftmp2 tmp;

      felem_mul tmp y1 ftmp2;
      felem_reduce ftmp6 tmp
    end
  else
    begin
      felem_assign ftmp3 x1;

      felem_assign ftmp5 z1;
      felem_scalar ftmp5 (u32 1);

      felem_assign ftmp6 y1
    end;

  smallfelem_mul tmp x2 small1;
  felem_reduce ftmp4 tmp;

  felem_diff_zero107 ftmp4 ftmp3;
  felem_shrink small4 ftmp4;

  let x_equal = smallfelem_is_zero small4 in

  felem_small_mul tmp small4 ftmp5;
  felem_reduce z_out tmp;

  smallfelem_mul tmp small1 small3;
  felem_reduce ftmp tmp;

  felem_small_mul tmp y2 ftmp;
  felem_reduce ftmp5 tmp;

  felem_diff_zero107 ftmp5 ftmp6;
  felem_scalar ftmp5 (u32 1);
  felem_shrink small1 ftmp5;
  let y_equal = smallfelem_is_zero small1 in

  let zero = u128(0) in
  if  ((x_equal <> zero) && (y_equal <> zero) && not(z1_is_zero <> zero) && not(z2_is_zero <> zero)) then
      begin
        point_double x3 y3 z3 x1 y1 z1
      end
  else
      begin
        felem_assign ftmp ftmp4;
        felem_scalar ftmp (u32 1);
        felem_square tmp ftmp;
        felem_reduce ftmp tmp;
        felem_mul tmp ftmp4 ftmp;
        felem_reduce ftmp2 tmp;
        felem_mul tmp ftmp3 ftmp;
        felem_reduce ftmp4 tmp;
        smallfelem_square tmp small1;
        felem_reduce x_out tmp;
        felem_assign ftmp3 ftmp4;
        felem_scalar ftmp4 (u32 1);
        felem_sum ftmp4 ftmp2;
        felem_diff x_out ftmp4;

        felem_diff_zero107 ftmp3 x_out;
        felem_small_mul tmp small1 ftmp3;
        felem_mul tmp2 ftmp6 ftmp2;
        longfelem_scalar tmp2 (u64 1);
        longfelem_diff tmp tmp2;
        felem_reduce_zero105 y_out tmp;

        copy_small_conditional x_out x2 z1_is_zero;
        copy_conditional x_out x1 z2_is_zero;
        copy_small_conditional y_out y2 z1_is_zero;
        copy_conditional y_out y1 z2_is_zero;
        copy_small_conditional z_out z2 z1_is_zero;
        copy_conditional z_out z1 z2_is_zero;
        felem_assign x3 x_out;
        felem_assign y3 y_out;
        felem_assign z3 z_out
      end
  )


val point_add_small:
  x3:smallfelem -> y3:smallfelem -> z3:smallfelem ->
  x1:smallfelem -> y1:smallfelem -> z1:smallfelem ->
  x2:smallfelem -> y2:smallfelem -> z2:smallfelem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))

let point_add_small x3 y3 z3 x1 y1 z1 x2 y2 z2 =
	alloc  #(uint_t U128) #(unit) #(v(size 24)) (size 24) (u128(0)) 
		[BufItem x1; BufItem y1; BufItem z1;
			BufItem x2; BufItem y2; BufItem z2] 
		[BufItem x3; BufItem y3; BufItem z3] 
    (fun h0 _ h1 -> True) (
      fun temp ->
  let felem_x3 = sub temp (size 0) (size 4) in
  let felem_y3 = sub temp (size 4) (size 4) in
  let felem_z3 = sub temp (size 8) (size 4) in
  let felem_x1 = sub temp (size 12) (size 4) in
  let felem_y1 = sub temp (size 16) (size 4) in
  let felem_z1 = sub temp (size 20) (size 4) in
  smallfelem_expand felem_x1 x1;
  smallfelem_expand felem_y1 y1;
  smallfelem_expand felem_z1 z1;
  point_add felem_x3 felem_y3 felem_z3 felem_x1 felem_y1 felem_z1 (u32 0) x2 y2 z2;
  felem_shrink x3 felem_x3;
  felem_shrink y3 felem_y3;
  felem_shrink z3 felem_z3
)
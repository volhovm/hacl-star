module Hacl.P256.Ladder

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
open Hacl.P256.PointAdd
open Hacl.P256.Inv

open Spec.Lib.IntBuf.LoadStore

let pointLength = size(12)

type point = lbuffer limb (v pointLength)

let get_x (p:point) = sub #_ #_ #(v(size 4)) p (size 0) (size 4)
let get_y (p:point) = sub #_ #_ #(v(size 4)) p (size 4) (size 4)
let get_z (p:point) = sub #_ #_ #(v(size 4)) p (size 8) (size 4)


// TODO: implement
let disjoint_p (p:point) (q:point) = True

private
val ith_bit:
  k:lbuffer (uint_t U8) (v (size 32)) ->
  i:size_t{size_v i < 256} ->
  Stack (uint_t U8)
    (requires (fun h -> True))
    (ensures (fun h0 z h1 -> True))

let ith_bit k i =
	assert_norm(pow2 1 = 2);
	assert_norm(pow2 3 = 8);
	assert_norm(pow2 5 = 32);
	assert_norm(pow2 8 = 256);

	let q = i /. size(8) in  
	let i = size_to_uint32 i in
		//assert(v q = v i / 8);
	let r = i &. (u32 7) in 
		//TODO: logand_mask instead of logand
	let i = logand i (u32 3) in 
 		// assert(v r = v i % 8);
  		//Math.Lemmas.lemma_div_lt (v i) 8 3;
	let kq = k.(q) in (* U8  *)
	let kq' = to_u8(kq >>. r) in
	let z = to_u8 (kq' &.  (u8 1)) in 
  	let kq' = logand kq' (u8 1) in 
		//assert(Hacl.UInt8.v z = (Hacl.UInt8.v kq / pow2 (v r)) % 2);
  	z

private inline_for_extraction 
let mk_mask (iswap: (uint_t U128)
	{uint_v iswap = 0 \/ uint_v iswap = 1}) :
  Tot (z:(uint_t U128)
		{if uint_v iswap = 1 then uint_v z = pow2 64 - 1 else uint_v z = 0})
  = let swap = (u128 0) -. iswap in
    	//assert_norm((0 - 1) % pow2 64 = pow2 64 - 1);
    	//assert_norm((0 - 0) % pow2 64 = 0);
    swap

private
val swap_cond_inplace:
  p:point -> q:point (*{disjoint_p p q}*) -> i:limb{uint_v i = 0 \/ uint_v i = 1} ->
  Stack unit
    (requires (fun h -> True (*) live h p /\ live h q /\
      ( let x1 = as_seq h (get_x p) in
        let y1 = as_seq h (get_y p) in
        let z1 = as_seq h (get_z p) in
        True) /\
        // red_513 x1 /\ red_513 y1 /\ red_513 z1) /\
      ( let x2 = as_seq h (get_x q) in
        let y2 = as_seq h (get_y q) in
        let z2 = as_seq h (get_z q) in
        True
        // red_513 x2 /\ red_513 y2 /\ red_513 z2
  ) ) *)))
    (ensures (fun h0 _ h1 -> True (*)

     live h1 p /\ live h1 q /\ modifies_2 p q h0 h1 /\ live h0 p /\ live h0 q /\
      ( let x1 = as_seq h0 (get_x p) in
        let y1 = as_seq h0 (get_y p) in
        let z1 = as_seq h0 (get_z p) in
        let x2 = as_seq h0 (get_x q) in
        let y2 = as_seq h0 (get_y q) in
        let z2 = as_seq h0 (get_z q) in
        let x1' = as_seq h1 (get_x p) in
        let y1' = as_seq h1 (get_y p) in
        let z1' = as_seq h1 (get_z p) in
        let x2' = as_seq h1 (get_x q) in
        let y2' = as_seq h1 (get_y q) in
        let z2' = as_seq h1 (get_z q) in
        True /\
      (if UInt128.v i = 1 then (x1' == x2 /\ y1' == y2 /\ z1' == z2 /\
                                    x2' == x1 /\ y2' == y1 /\ z2' == z1)
         else (x1' == x1 /\ y1' == y1 /\ z1' == z1 /\
               x2' == x2 /\ y2' == y2 /\ z2' == z2))) *) 
    ))

let swap_cond_inplace p q iswap =
  let mask = mk_mask iswap in
  let inv (h1:mem) (i:nat) = True in
  let f (i:size_t) : Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True)) = 
      let pi = p.(i) in
      let qi = q.(i) in
      let x  = mask &. (pi ^. qi) in
      let pi' = pi ^. x in
      let qi' = qi ^. x in
      p.(i) <- pi';
      q.(i) <- qi'
      in
  for (size 0) (size 12) inv f

val loop_step:
  pp:point ->
  ppq:point ->
  p:point ->
  pq:point ->
  k:lbuffer (uint_t U8) (v (size 32)) ->
  i:size_t ->
  Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))

let loop_step pp ppq p pq k i =
	alloc #(uint_t U64) #(unit) #(v(size 12)) (size 12) (u64(0)) 
		[BufItem p; BufItem pq; BufItem k] [BufItem ppq; BufItem pp] 
		(fun h0 _ h1 -> True) (
			fun tmp -> 
  let x = sub tmp (size 0) (size 4) in
  let y = sub tmp (size 4) (size 4) in
  let z = sub tmp (size 8) (size 4) in
  (*) TODO: change the algorithm, this is an ugly workaround due to OpenSSL's 'point_add' function*)
  let ith_bit = ith_bit k i in
  let ith_bit = to_u128 ith_bit in
  swap_cond_inplace p pq ith_bit;
  felem_shrink x (get_x pq);
  felem_shrink y (get_y pq);
  felem_shrink z (get_z pq);
  point_double (get_x pp) (get_y pp) (get_z pp) (get_x p) (get_y p) (get_z p);
  point_add (get_x ppq) (get_y ppq) (get_z ppq)
            (get_x p) (get_y p) (get_z p)
            (u32 0) x y z;
           // (get_x pq) (get_y pq) (get_z pq);
  // let x0 = x.(0ul) in
  // let x1 = x.(1ul) in
  // let x2 = x.(2ul) in
  // let x3 = x.(3ul) in
  // ppq.(size 0) <- to_u128 x0;
  // ppq.(size 1) <- to_u128 x1;
  // ppq.(size 2) <- to_u128 x2;
  // ppq.(size 3) <- to_u128 x3;
  swap_cond_inplace pp ppq ith_bit
)


val point_mul_:
  pp:point ->
  ppq:point ->
  p:point ->
  pq:point ->
	k:lbuffer (uint_t U8) (v (size 32)) ->
  Stack unit
    (requires (fun h -> live h k /\ True))
    (ensures (fun h0 _ h1 -> True (*live h0 k*)))

let point_mul_ pp ppq p pq k =
	//let h0 = ST.get() in
	let inv (h1:mem) (i:nat) = True in
	let f' (i:size_t{size_v i >= 0 /\ size_v i < 256}): Stack unit
	    (requires (fun h -> True (*) inv h (UInt32.v i *)))
	    (ensures (fun h_1 _ h_2 -> True (*) FStar.UInt32.(inv h_2 (v i + 1)) *))) =
	    loop_step pp ppq p pq k (size_sub (size 256) (size_incr (size_sl i (u32 2))));
	    loop_step p pq pp ppq k (size_sub (size 256) (size_incr (size_incr (size_sl i (u32 2))))) in
	    for (size 0) (size 128) inv f'

val p256:
  outx:lbuffer (uint_t U8) (v (size 32)) ->
  outy:lbuffer (uint_t U8) (v (size 32)) ->
  inx:lbuffer (uint_t U8) (v (size 32)) ->
  iny:lbuffer (uint_t U8) (v (size 32)) ->
  key:lbuffer (uint_t U8) (v (size 32)) ->
  Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))

let p256 outx outy inx iny key =
	let zero = (u128 0) in 
	let q = create (pointLength) zero in
	//WHY?
	let qx = get_x q in 
	let qy = get_y q in
	let qz = get_z q in
	uints_from_bytes_le qx inx; 
	uints_from_bytes_le qy iny;
	qz.(size 0) <- (u128 1);

	let p = create (pointLength) zero in
	let px = get_x p in
	let py = get_y p in
	px.(size 0) <- u128 1;
	py.(size 0) <- u128 1;

	let pp = create (pointLength) zero in
  	let ppq = create (pointLength) zero in
  	point_mul_ pp ppq p q key;

  	let x = create (size 4) (u64 0) in
	let y = create (size 4) (u64 0) in
	let tmp = create (size 8) zero in
	let z2 = create (size 4) zero in
	let z3 = create (size 4) zero in
	let z2_inv = create (size 4) zero in
	let z3_inv = create (size 4) zero in
	let big_x = create (size 4) zero in
	let big_y = create (size 4) zero in
  	
  	felem_square tmp (get_z p);
	felem_reduce z2 tmp;
	felem_inv z2_inv z2;
	felem_mul tmp (get_x p) z2_inv;
	felem_reduce big_x tmp;
	felem_contract x big_x;
  
	felem_mul tmp z2 (get_z p);
	felem_reduce z3 tmp;
	felem_inv z3_inv z3;
	felem_mul tmp (get_y p) z3_inv;
	felem_reduce big_y tmp;
	felem_contract y big_y;

	uints_to_bytes_le outx x;
	uints_to_bytes_le outy y
  (*)	


  let qx3 = load64_be (Buffer.sub inx 0ul 8ul) in
  let qx2 = load64_be (Buffer.sub inx 8ul 8ul) in
  let qx1 = load64_be (Buffer.sub inx 16ul 8ul) in
  let qx0 = load64_be (Buffer.sub inx 24ul 8ul) in
  let qy3 = load64_be (Buffer.sub iny 0ul 8ul) in
  let qy2 = load64_be (Buffer.sub iny 8ul 8ul) in
  let qy1 = load64_be (Buffer.sub iny 16ul 8ul) in
  let qy0 = load64_be (Buffer.sub iny 24ul 8ul) in
  qx.(0ul) <- UInt128.uint64_to_uint128 qx0;
  qx.(1ul) <- UInt128.uint64_to_uint128 qx1;
  qx.(2ul) <- UInt128.uint64_to_uint128 qx2;
  qx.(3ul) <- UInt128.uint64_to_uint128 qx3;
  qy.(0ul) <- UInt128.uint64_to_uint128 qy0;
  qy.(1ul) <- UInt128.uint64_to_uint128 qy1;
  qy.(2ul) <- UInt128.uint64_to_uint128 qy2;
  qy.(3ul) <- UInt128.uint64_to_uint128 qy3;
  qz.(0ul) <- UInt128.uint64_to_uint128 1uL;
  // Create point at infinity
  let p = create (UInt128.uint64_to_uint128 0uL) 12ul in
  let px = get_x p in
  let py = get_y p in
  px.(0ul) <- UInt128.uint64_to_uint128 1uL;
  py.(0ul) <- UInt128.uint64_to_uint128 1uL;
  let pp = create (UInt128.uint64_to_uint128 0uL) 12ul in
  let ppq = create (UInt128.uint64_to_uint128 0uL) 12ul in
  point_mul_ pp ppq p q key;
  
  let x = create 0uL 4ul in
  let y = create 0uL 4ul in
  let tmp = create (UInt128.uint64_to_uint128 0uL) 8ul in
  let z2 = create (UInt128.uint64_to_uint128 0uL) 4ul in
  let z3 = create (UInt128.uint64_to_uint128 0uL) 4ul in
  let z2_inv = create (UInt128.uint64_to_uint128 0uL) 4ul in
  let z3_inv = create (UInt128.uint64_to_uint128 0uL) 4ul in
  let big_x = create (UInt128.uint64_to_uint128 0uL) 4ul in
  let big_y = create (UInt128.uint64_to_uint128 0uL) 4ul in
  
  felem_square tmp (get_z p);
  felem_reduce z2 tmp;
  felem_inv z2_inv z2;
  felem_mul tmp (get_x p) z2_inv;
  felem_reduce big_x tmp;
  felem_contract x big_x;
  
  felem_mul tmp z2 (get_z p);
  felem_reduce z3 tmp;
  felem_inv z3_inv z3;
  felem_mul tmp (get_y p) z3_inv;
  felem_reduce big_y tmp;
  felem_contract y big_y;
  
  let x0 = x.(0ul) in
  let x1 = x.(1ul) in
  let x2 = x.(2ul) in
  let x3 = x.(3ul) in
  let y0 = y.(0ul) in
  let y1 = y.(1ul) in
  let y2 = y.(2ul) in
  let y3 = y.(3ul) in
  store64_be (Buffer.sub outx 0ul 8ul) x3;
  store64_be (Buffer.sub outx 8ul 8ul) x2;
  store64_be (Buffer.sub outx 16ul 8ul) x1;
  store64_be (Buffer.sub outx 24ul 8ul) x0;
  store64_be (Buffer.sub outy 0ul 8ul) y3;
  store64_be (Buffer.sub outy 8ul 8ul) y2;
  store64_be (Buffer.sub outy 16ul 8ul) y1;
  store64_be (Buffer.sub outy 24ul 8ul) y0;
  pop_frame()

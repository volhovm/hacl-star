module Hacl.P256.Shrink 

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

open FStar.Math.Lemmas

assume val lemma_4_pows: a: nat {a < pow2 126} -> b: nat {b < pow2 126} -> c: nat {c < pow2 126} ->
	Lemma(a + b + c < pow2 128)

#set-options " --z3rlimit 100 --initial_fuel 2"

(*inline_for_extraction val alloc: #a:Type0 -> #b:Type0 -> len:size_t -> init:a -> 
		 reads:list bufitem ->
		 writes:list bufitem ->
		 spec:(h0:mem -> r:b -> h1:mem -> Type) ->
		 impl:(buf:lbuffer a len -> Stack b
			   (requires (fun h -> live h buf /\ live_list h reads /\ live_list h writes /\ disjoint_list buf reads /\ disjoint_list buf writes))
			   (ensures (fun h0 r h1 -> preserves_live h0 h1 /\
						 modifies (BufItem buf :: writes) h0 h1 /\
						 spec h0 r h1))) ->
		    Stack b
		      (requires (fun h0 -> live_list h0 reads /\ live_list h0 writes))
		      (ensures (fun h0 r h1 -> preserves_live h0 h1 /\ 
					    modifies writes h0 h1 /\
					    spec h0 r h1)) *)



val felem_shrink:
  out:smallfelem -> input:felem ->Stack unit
  	(requires fun h -> True)
  	(ensures fun h0 _ h1 -> True)

let felem_shrink out input = 
	alloc 4 (u128(0)) [BufItem input] [BufItem out] 
		(fun h0 _ h1 -> True) (
			fun tmp -> 
	let zero110 = zero110 () in
  	let kPrime  = kPrime () in
  	let kPrime3Test = u64(0x7fffffff00000001) in 
	let input0 = input.(0) in
	let input1 = input.(1) in
	let input2 = input.(2) in
	let input3 = input.(3) in
	let zero0  = zero110.(0) in
	let zero1  = zero110.(1) in
	let zero2  = zero110.(2) in
	let zero3  = zero110.(3) in
	let kPrime0 = kPrime.(0) in
	let kPrime1 = kPrime.(1) in
	let kPrime2 = kPrime.(2) in
	let kPrime3 = kPrime.(3) in 
	let tmp3 = zero3 +! input3 +! (input2 >>. u32(64)) in
  	let tmp2 = zero2 +! (to_u128 (to_u64 input2)) in
  	let tmp0 = zero0 +! input0 in
  	let tmp1 = zero1 +! input1 in
   	let a = tmp3 >>. u32(64) in
  	let tmp3 = to_u128 (to_u64 tmp3) in
  	let tmp3 = tmp3 -! a in
 	let tmp3 = tmp3 +! (a <<. u32(32)) in
	let b = a in
	let a = tmp3 >>. u32(64) in
	let b = b +! a in
	let tmp3 = to_u128 (to_u64 tmp3) in
	let tmp3 = tmp3 -! a in
	let tmp3 = tmp3 +! (a <<. u32(32)) in
  	let tmp0 = tmp0 +! b in
  	let tmp1 = tmp1 -! (b <<. u32(32)) in
 	let high = to_u64 (gte_mask tmp3 (load128 (u64(0x1)) (u64(0x0)))) in
	let low = to_u64 tmp3 in
  	let mask = gte_mask low (u64(0x8000000000000000)) in
	let low = to_u64(low &. (u64(0x7fffffffffffffff))) in
	let low = gte_mask kPrime3Test low in
	let low = lognot low in
	let mask = to_u64((mask &. low) |. high) in
	let tmp0 = tmp0 -! to_u128 (to_u64(mask &. kPrime0)) in
	let tmp1 = tmp1 -! to_u128 (to_u64(mask &. kPrime1)) in
	let tmp3 = tmp3 -! to_u128 (to_u64(mask &. kPrime3)) in
	let tmp1 = tmp1 +! (tmp0 >>. u32(64)) in
	let tmp0 = to_u64 tmp0 in
	let tmp2 = tmp2 +! (tmp1 >>. u32(64)) in
	let tmp1 = to_u64 tmp1 in
	let tmp3 = tmp3 +! (tmp2 >>. u32(64)) in
	let tmp2 = to_u64 tmp2 in
	out.(0) <- tmp0;
	out.(1) <- tmp1;
	out.(2) <- tmp2;
	out.(3) <- to_u64 tmp3)



(*)
val felem_shrink:
  out:smallfelem -> input:felem -> temp: lbuffer limb 8-> 
  temp2 : lbuffer uint64 nlimbs->  Stack unit
    (requires (fun h -> live h out /\ live h input /\  live h temp /\ live h temp2 /\ 
    	disjoint input out /\ disjoint input temp /\ disjoint input temp2 /\
    	disjoint temp temp2 /\ disjoint temp out /\ disjoint temp input /\
    	(let input = as_lseq input h in 
     		let input0 = Spec.Lib.IntSeq.index input 0 in 
     		let input1 = Spec.Lib.IntSeq.index input 1 in 
     		let input2 = Spec.Lib.IntSeq.index input 2 in 
     		let input3 = Spec.Lib.IntSeq.index input 3 in 
     		uint_v input0 < pow2 109 /\
     		uint_v input1 < pow2 109 /\
     		uint_v input2 < pow2 109 /\
     		uint_v input3 < pow2 109 
     	)
    ))
    (ensures (fun h0 _ h1 -> True))

let felem_shrink out input temp temp2=
	let tmp = sub temp 4 4 in 
	let zero110 = sub temp 0 4 in 
		zero110_2 zero110;
	let kPrimeA = sub temp2 0 4 in 
		kPrime kPrimeA; 
	let kPrime3Test = u64(0x7fffffff00000001) in 
	let input0 = input.(0) in
	let input1 = input.(1) in
	let input2 = input.(2) in
	let input3 = input.(3) in
	let zero0  = zero110.(0) in
	let zero1  = zero110.(1) in
	let zero2  = zero110.(2) in
	let zero3  = zero110.(3) in
	let kPrime0 = kPrimeA.(0) in
	let kPrime1 = kPrimeA.(1) in
	let kPrime2 = kPrimeA.(2) in
	let kPrime3 = kPrimeA.(3) in
	
	let temp = shift_right input2 (u32(64)) in 
	let temp = to_u64(temp) in 
	let temp = to_u128(temp) in 
	  	assert_norm (uint_v two64m32 < pow2 64);
  		(*assert_norm(pow2 109 + pow2 64 + pow2 64 < pow2 128);*)
  		assert(uint_v input3 < pow2 109);
  		assert(uint_v zero3 < pow2 109);
  		assert(uint_v temp < pow2 109);
  	lemma_4_pows (uint_v zero3) 
  		(uint_v input3) 
  			(uint_v temp);

	tmp.(3) <- zero3 +! input3 +! temp;admit();

		let temp = to_u64(input2) in 
		let temp = to_u128(temp) in 
	tmp.(2) <- zero2 +! temp;
	tmp.(0) <- zero0 +! input0;
	
	assert_norm(uint_v two110p32m0 < pow2 111);
	assert_norm(pow2 111 + pow2 109 < pow2 128);
	tmp.(1) <- zero1 +! input1

(*)
assume val lemmaPowAsMinus: a: nat -> b: nat{a >= b} -> Lemma (pow2 a / pow2 b = pow2 (a-b))

val felem_shrink2: tmp: lbuffer limb 8->  Stack unit
	(requires 
		(fun h0 -> live h0 tmp /\ 
			(
			let input = sub tmp 4 4 in 
			let input = as_lseq input h0 in 
     		let input0 = Spec.Lib.IntSeq.index input 0 in 
     		let input1 = Spec.Lib.IntSeq.index input 1 in 
     		let input3 = Spec.Lib.IntSeq.index input 3 in 
     		uint_v input0 < pow2 110 /\ 
     		uint_v input0 >= pow2 64/\

     		uint_v input1 > pow2 110 /\
     		uint_v input3 < pow2 11
     	)
		))
	(ensures 
		(fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 tmp h0 h1)
	)

let felem_shrink2 tmp  = 
	let tmp = sub tmp 4 4 in
	let tmp0 = tmp.(0) in 
	let tmp3 = tmp.(3) in 
	let a = shift_right tmp3 (u32(64)) in
	let temp = to_u64(tmp3) in
	let tmp3 = to_u128(temp) in 
	let temp = shift_left a (u32(32)) in
	let temp = temp -! a in
	let tmp3 = tmp3 +! temp in 
	let b = a in
	let a = shift_right tmp3 (u32(64)) in 
	let b = b +! a in 
	let temp = to_u64 (tmp3) in  
	let tmp3 = to_u128 (temp) in 
	let temp = shift_left a (u32(32)) in
	let temp = temp -! a in 
	let tmp3 = tmp3 +! temp in 
	let tmp0 = tmp0 +! b in 
	tmp.(0) <- tmp0;
	let tmp1 = tmp.(1) in 
	let temp = shift_left b (u32(32)) in 
	let tmp1 = tmp1 -! temp in 
	tmp.(1) <- tmp1;
	tmp.(3) <- tmp3
(*)
val felem_shrink3: temp: lbuffer limb 8-> temp2: smallfelem -> 
	b:limb{uint_v b < pow2 47} -> 
	out:smallfelem ->   Stack unit
	(requires 
		(fun h0 -> live h0 temp /\ live h0 temp2 
			/\ disjoint out temp /\ disjoint temp out /\ 
			disjoint out temp2 /\ disjoint temp2 out /\
			disjoint temp temp2 /\ disjoint temp2 temp /\
			(
			let input = sub temp 4 4 in 
			let input = as_lseq input h0 in 
     		let input0 = Spec.Lib.IntSeq.index input 0 in 
     		let input1 = Spec.Lib.IntSeq.index input 1 in 
     		let input3 = Spec.Lib.IntSeq.index input 3 in 
     		uint_v input0 < pow2 110 /\
     		uint_v input0 >= pow2 64 /\
     		uint_v input1 > pow2 109

     	)
		 ))
	(ensures 
		(fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 temp h0 h1)
	)
(*)
let felem_shrink3 temp temp2 b out = 
	let tmp = sub temp 4 4 in
	let kPrimeA = temp2 in 
		kPrime kPrimeA; 

	let kPrime0 = kPrimeA.(0) in
	let kPrime1 = kPrimeA.(1) in
	let kPrime2 = kPrimeA.(2) in
	let kPrime3 = kPrimeA.(3) in
	let kPrime3Test = u64(0x7fffffff00000001) in 

	let tmp3 = tmp.(3) in 

  // TODO: better implementation
  // let high = tmp3 >>. 64ul in
  		let pow2_64 = load128 (u64(1)) (u64(0)) in 
  		let temp = gte_mask tmp3 pow2_64 in 
	let high = to_u64 temp in 

  // TODO: better implementation
	let low = to_u64 tmp3 in
	let mask = gte_mask low (u64(0x8000000000000000)) in

	let low = gte_mask kPrime3Test low in
	let low = lognot low in

	let mask = (logor (logand mask low) high) in

	let tmp0 = tmp.(0) in
	let tmp0 = tmp0 -! (to_u128 (logand mask kPrime0)) in admit();
	let tmp1 = tmp.(1) in 
	let tmp1 = tmp1 -! (to_u128 (logand mask kPrime1)) in admit();
	let tmp3 = tmp3 -! to_u128 (logand mask kPrime3) in

	let sixtyfour = u32(64) in 

	let tmp1 = tmp1 +! (shift_right tmp0 (sixtyfour)) in
	let tmp0 = to_u64 tmp0 in
	let tmp2 = tmp.(2) in 
	let tmp2 = tmp2 +! (shift_right tmp1 sixtyfour) in
	let tmp1 = to_u64 tmp1 in
	let tmp3 = tmp3 +! (shift_right tmp2 sixtyfour) in
	let tmp2 = to_u64 tmp2 in

  out.(0) <- tmp0;
  out.(1) <- tmp1;
  out.(2) <- tmp2;
  out.(3) <- to_u64(tmp3)
module Hacl.P256.SmallNegation

open FStar.Mul

open FStar.HyperStack
open FStar.HyperStack.ST

open Spec.Lib
open Spec.Lib.IntSeq
open Spec.Lib.IntBuf
open Spec.Lib.IntTypes

open Spec.Lib.IntSeq.Lemmas
open Spec.Lib.IntBuf.Lemmas

open P256.S
open Hacl.P256.Zeros

#set-options " --z3rlimit 200 "


val smallfelem_neg: out:felem -> small:smallfelem ->tempBuffer: felem ->  Stack unit
  (requires (fun h -> live h out /\ live h small /\ live h tempBuffer))
  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies2 out tempBuffer h0 h1 )) (* /\ modifies1 out h0 h1*)

let smallfelem_neg out small tempBuffer =
	zero105_2 tempBuffer;
	let small0 = small.(0) in
	let small1 = small.(1) in
	let small2 = small.(2) in
	let small3 = small.(3) in
	let zero0  = tempBuffer.(0) in
	let zero1  = tempBuffer.(1) in
	let zero2  = tempBuffer.(2) in
	let zero3  = tempBuffer.(3) in
		assert((uint_v zero0) >= (uint_v small0));
		assert((uint_v zero1) >= (uint_v small1));
		assert((uint_v zero2) >= (uint_v small2));
		assert((uint_v zero3) >= (uint_v small3));
	out.(0) <- sub zero0 (to_u128 (small0));
	out.(1) <- sub zero0 (to_u128 (small1));
	out.(2) <- sub zero0 (to_u128 (small2));
	out.(3) <- sub zero0 (to_u128 (small3))


val felem_diff: out:felem -> input:felem -> 
	tempBuffer: felem -> Stack unit
    (requires (fun h -> live h out /\ live h input /\ live h tempBuffer /\
     	disjoint out tempBuffer /\ disjoint input tempBuffer /\
     	(let input = as_lseq input h in 
     		let input0 = Spec.Lib.IntSeq.index input 0 in 
     		let input1 = Spec.Lib.IntSeq.index input 1 in 
     		let input2 = Spec.Lib.IntSeq.index input 2 in 
     		let input3 = Spec.Lib.IntSeq.index input 3 in 
     		uint_v input0 < pow2 104 /\
     		uint_v input1 < pow2 104 /\
     		uint_v input2 < pow2 104 /\
     		uint_v input3 < pow2 104 
     	)
     	/\
    	(let out = as_lseq out h in 
    	let out0 = Spec.Lib.IntSeq.index out 0 in 
    	let out1 = Spec.Lib.IntSeq.index out 1 in 
    	let out2 = Spec.Lib.IntSeq.index out 2 in 
    	let out3 = Spec.Lib.IntSeq.index out 3 in 
     	uint_v out0 < pow2 128 - (uint_v two105m41m9) /\
    	uint_v out1 < pow2 128 - (uint_v two105) /\
		uint_v out2 < pow2 128 - (uint_v two105m41p9) /\
		uint_v out3 < pow2 128 - (uint_v two105m41p9)
				))
	)
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies2 tempBuffer out h0 h1))

#set-options " --z3rlimit 500 "

let felem_diff out input tempBuffer=
zero105_2 tempBuffer;
  let input0 = input.(0) in
  let input1 = input.(1) in
  let input2 = input.(2) in
  let input3 = input.(3) in
	let out0 = index out 0 in 
	let out1 = index out 1 in 
	let out2 = index out 2 in 
	let out3 = index out 3 in 
  let zero0  = tempBuffer.(0) in
  let zero1  = tempBuffer.(1) in
  let zero2  = tempBuffer.(2) in 
  let zero3  = tempBuffer.(3) in
  let out0 = add zero0 out0 in
  let out1 = add zero1 out1 in
  let out2 = add zero2 out2 in
  let out3 = add zero3 out3 in
	  assert_norm (uint_v two105m41m9 > pow2 104);
	  assert_norm (uint_v two105 > pow2 104);
	  assert_norm (uint_v two105m41p9 > pow2 104);
  out.(0) <- sub out0 input0;
  out.(1) <- sub out1 input1;
  out.(2) <- sub out2 input2;
  out.(3) <- sub out3 input3
 


val felem_diff_zero107:
  out:felem -> input:felem -> 
	tempBuffer: felem -> Stack unit
    (requires (fun h -> live h out /\ live h input /\ live h tempBuffer /\
     	disjoint out tempBuffer /\ disjoint input tempBuffer /\
     	(let input = as_lseq input h in 
     		let input0 = Spec.Lib.IntSeq.index input 0 in 
     		let input1 = Spec.Lib.IntSeq.index input 1 in 
     		let input2 = Spec.Lib.IntSeq.index input 2 in 
     		let input3 = Spec.Lib.IntSeq.index input 3 in 
     		uint_v input0 < pow2 106 /\
     		uint_v input1 < pow2 106 /\
     		uint_v input2 < pow2 106 /\
     		uint_v input3 < pow2 106 
     	)
     	/\
    	(let out = as_lseq out h in 
    	let out0 = Spec.Lib.IntSeq.index out 0 in 
    	let out1 = Spec.Lib.IntSeq.index out 1 in 
    	let out2 = Spec.Lib.IntSeq.index out 2 in 
    	let out3 = Spec.Lib.IntSeq.index out 3 in 
     	uint_v out0 < pow2 128 - (uint_v two107m43m11) /\
    	uint_v out1 < pow2 128 - (uint_v two107) /\
		uint_v out2 < pow2 128 - (uint_v two107m43p11) /\
		uint_v out3 < pow2 128 - (uint_v two107m43p11)
				))
	)
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies2 tempBuffer out h0 h1))


let felem_diff_zero107 out input tempBuffer=
zero107_2 tempBuffer;
  let input0 = input.(0) in
  let input1 = input.(1) in
  let input2 = input.(2) in
  let input3 = input.(3) in
	let out0 = index out 0 in 
	let out1 = index out 1 in 
	let out2 = index out 2 in 
	let out3 = index out 3 in 
  let zero0  = tempBuffer.(0) in
  let zero1  = tempBuffer.(1) in
  let zero2  = tempBuffer.(2) in 
  let zero3  = tempBuffer.(3) in
  let out0 = add zero0 out0 in
  let out1 = add zero1 out1 in
  let out2 = add zero2 out2 in
  let out3 = add zero3 out3 in
	  assert_norm (uint_v two107m43m11 > pow2 106);
	  assert_norm (uint_v two107 > pow2 106);
	  assert_norm (uint_v two107m43p11 > pow2 106);
  out.(0) <- sub out0 input0;
  out.(1) <- sub out1 input1;
  out.(2) <- sub out2 input2;
  out.(3) <- sub out3 input3

val longfelem_diff:
  out:longfelem -> input:longfelem ->
   Stack unit
    (requires (fun h -> live h out /\ live h input 
    	 /\
     	(let input = as_lseq input h in 
     		let input0 = Spec.Lib.IntSeq.index input 0 in 
     		let input1 = Spec.Lib.IntSeq.index input 1 in 
     		let input2 = Spec.Lib.IntSeq.index input 2 in 
     		let input3 = Spec.Lib.IntSeq.index input 3 in 
     		let input4 = Spec.Lib.IntSeq.index input 4 in 
     		let input5 = Spec.Lib.IntSeq.index input 5 in 
     		let input6 = Spec.Lib.IntSeq.index input 6 in 
     		let input7 = Spec.Lib.IntSeq.index input 7 in 
     		uint_v input0 < 7 * pow2 67 /\
     		uint_v input1 < 7 * pow2 67 /\
     		uint_v input2 < 7 * pow2 67 /\
     		uint_v input3 < 7 * pow2 67 /\
     		uint_v input4 < 7 * pow2 67 /\
     		uint_v input5 < 7 * pow2 67 /\
     		uint_v input6 < 7 * pow2 67 /\
     		uint_v input7 < 7 * pow2 67 
     	)	
    	/\
    	(let out = as_lseq out h in 
    	let out0 = Spec.Lib.IntSeq.index out 0 in 
    	let out1 = Spec.Lib.IntSeq.index out 1 in 
    	let out2 = Spec.Lib.IntSeq.index out 2 in 
    	let out3 = Spec.Lib.IntSeq.index out 3 in 
		let out4 = Spec.Lib.IntSeq.index out 4 in 
		let out5 = Spec.Lib.IntSeq.index out 5 in 
		let out6 = Spec.Lib.IntSeq.index out 6 in 
		let out7 = Spec.Lib.IntSeq.index out 7 in 
     	uint_v out0 < pow2 128 - (uint_v two70m8p6) /\
    	uint_v out1 < pow2 128 - (uint_v two70p40) /\
		uint_v out2 < pow2 128 - (uint_v two70) /\
		uint_v out3 < pow2 128 - (uint_v two70m40m38p6) /\
		uint_v out4 < pow2 128 - (uint_v two70m6) /\
		uint_v out5 < pow2 128 - (uint_v two70m6) /\
		uint_v out6 < pow2 128 - (uint_v two70m6) /\
		uint_v out7 < pow2 128 - (uint_v two70m6) 
	)

    ))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 out h0 h1))

let longfelem_diff out input =
  let input0 = input.(0) in
  let input1 = input.(1) in
  let input2 = input.(2) in
  let input3 = input.(3) in
  let input4 = input.(4) in
  let input5 = input.(5) in
  let input6 = input.(6) in
  let input7 = input.(7) in
  let out0 = out.(0) in
  let out1 = out.(1) in
  let out2 = out.(2) in
  let out3 = out.(3) in
  let out4 = out.(4) in
  let out5 = out.(5) in
  let out6 = out.(6) in
  let out7 = out.(7) in
  let out0 = add two70m8p6 out0 in
  let out1 = add two70p40 out1 in
  let out2 = add two70 out2 in
  let out3 = add two70m40m38p6 out3 in
  let out4 = add two70m6 out4 in
  let out5 = add two70m6 out5 in
  let out6 = add two70m6 out6 in
  let out7 = add two70m6 out7 in

	assert_norm(uint_v two70m8p6 > pow2 70 - pow2 40 - pow2 38);
	assert_norm(uint_v two70p40 >  pow2 70 - pow2 40 - pow2 38);
	assert_norm(uint_v two70 >  pow2 70 - pow2 40 - pow2 38);
	assert_norm(uint_v two70m40m38p6 >  pow2 70 - pow2 40 - pow2 38);
	assert_norm(uint_v two70m6 >  pow2 70 - pow2 40 - pow2 38);

	assert_norm(7 * pow2 67 <  pow2 70 - pow2 40 - pow2 38);	

  out.(0) <- sub out0 input0;
  out.(1) <- sub out1 input1;
  out.(2) <- sub out2 input2;
  out.(3) <- sub out3 input3;
  out.(4) <- sub out4 input4;
  out.(5) <- sub out5 input5;
  out.(6) <- sub out6 input6;
  out.(7) <- sub out7 input7

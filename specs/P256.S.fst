module P256.S

open FStar.Mul

open FStar.HyperStack
open FStar.HyperStack.ST

open Spec.Lib
open Spec.Lib.IntBuf
open Spec.Lib.IntTypes



module Buffer = Spec.Lib.IntBuf

(* Constants *)
let nlimbs = 4
let nlimbs' = 4ul

(* Type aliases *)
type limb = uint128


type felem = lbuffer limb nlimbs
type longfelem = lbuffer limb (2 * nlimbs)
type smallfelem = lbuffer uint64 nlimbs

val create_felem: unit -> Stack (felem)
    (requires (fun h -> True))
    (ensures (fun h0 buf h1 -> creates1 buf h0 h1 /\ preserves_live h0 h1 ))

let create_felem () =
 	let zero = u128(0) in create nlimbs zero

val create_longfelem: unit -> Stack longfelem
    (requires (fun h -> True))
    (ensures (fun h0 buf h1 -> creates1 buf h0 h1  /\ preserves_live h0 h1))

let create_longfelem () =
	let zero = u128(0) in create (nlimbs*2) zero
  	

val create_smallfelem: unit -> Stack smallfelem
    (requires (fun h -> True))
    (ensures (fun h0 buf h1 -> creates1 buf h0 h1 /\ preserves_live h0 h1 ))

let create_smallfelem () =
  	let zero = u64(0) in create nlimbs zero 

val kPrime: unit -> 
  Stack smallfelem
    (requires (fun h -> True))
    (ensures (fun h0 b h1 -> True))

let kPrime () = 
	let b = createL [(u64(0xffffffffffffffff)); (u64(0xffffffff)); (u64(0x0)); (u64(0xffffffff00000001))] in 
	b	


val bin32_to_felem:
  output:felem -> input:lbuffer uint8 32 ->
  Stack unit
    (requires (fun h -> live h output /\ live h input))
    (ensures (fun h0 _ h1 ->  live h1 output /\ live h1 input /\ 
		preserves_live h0 h1 (*) /\ modifies1 output h0 h1*)
    	))

let bin32_to_felem output input = 
	let zero = u64(0) in 
	alloc 4 zero [BufItem output; BufItem input] 
		(fun h0 _ h1 -> True

		)	

		(fun tempBuffer -> 
			let h0 = FStar.HyperStack.ST.get () in 
				//assume (live h0 input);
			Buffer.uints_from_bytes_le tempBuffer input;		
			output.(0) <- to_u128 (tempBuffer.(0));
			output.(1) <- to_u128 (tempBuffer.(1));
			output.(2) <- to_u128 (tempBuffer.(2));
			output.(3) <- to_u128 (tempBuffer.(3))
		)

assume val uints_to_bytes_le:
	o:lbuffer uint8 32 ->i:lbuffer uint64 4 -> 
  	Stack unit 
		(requires (fun h0 -> live h0 o /\ live h0 i))
		(ensures (fun h0 _ h1 -> preserves_live h0 h1 /\
			modifies1 o h0 h1 ))

val smallfelem_to_bin32:
  output:lbuffer uint8 32 -> input:smallfelem ->
  Stack unit
    (requires (fun h -> live h output /\ live h input))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 output h0 h1))

(* uint 64 -> u8*)
let smallfelem_to_bin32 output input =
  uints_to_bytes_le output input

(*TO DO - Flip Endian *)

val smallfelem_one: out:smallfelem ->
	Stack unit
	    (requires (fun h -> live h out))
	    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 out h0 h1))

let smallfelem_one out =
  out.(0) <- u64(1);
  out.(1) <- u64(0);
  out.(2) <- u64(0);
  out.(3) <- u64(0)

val smallfelem_assign: out:smallfelem -> input:smallfelem ->
  Stack unit
    (requires (fun h -> live h out /\ live h input))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 out h0 h1))

let smallfelem_assign out input =
  let in0 = input.(0) in
  let in1 = input.(1) in
  let in2 = input.(2) in
  let in3 = input.(3) in
  out.(0) <- in0;
  out.(1) <- in1;
  out.(2) <- in2;
  out.(3) <- in3

val felem_assign: out:felem -> input:felem ->
  Stack unit
    (requires (fun h -> live h out /\ live h input))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 out h0 h1))

let felem_assign out input =
  let in0 = input.(0) in
  let in1 = input.(1) in
  let in2 = input.(2) in
  let in3 = input.(3) in
  out.(0) <- in0;
  out.(1) <- in1;
  out.(2) <- in2;
  out.(3) <- in3


val felem_sum: out:felem -> input:felem ->
  Stack unit
    (requires (fun h -> live h out /\ live h input))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 out h0 h1))

(*Or Add without mod?*)
let felem_sum out input =
  let in0 = input.(0) in
  let in1 = input.(1) in
  let in2 = input.(2) in
  let in3 = input.(3) in
  let o0 = out.(0) in
  let o1 = out.(1) in
  let o2 = out.(2) in
  let o3 = out.(3) in
  out.(0) <- add_mod o0 in0;
  out.(1) <- add_mod o1 in1;
  out.(2) <- add_mod o2 in2;
  out.(3) <- add_mod o3 in3

(*)
val felem_sum2: out:felem -> input:felem ->
  Stack unit
    (requires (fun h -> live h out /\ live h input))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 out h0 h1))

(*Or Add without mod?*)
let felem_sum2 out input =
  let in0 = input.(0) in
  let in1 = input.(1) in
  let in2 = input.(2) in
  let in3 = input.(3) in
  let o0 = out.(0) in
  let o1 = out.(1) in
  let o2 = out.(2) in
  let o3 = out.(3) in
  out.(0) <- add o0 in0;
  out.(1) <- add o1 in1;
  out.(2) <- add o2 in2;
  out.(3) <- add o3 in3
*)

val felem_small_sum: out:felem -> input:smallfelem ->
  Stack unit
    (requires (fun h -> live h out /\ live h input))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 out h0 h1))

let felem_small_sum out input =
  let in0 = input.(0) in
  let in1 = input.(1) in
  let in2 = input.(2) in
  let in3 = input.(3) in
  let o0 = out.(0) in
  let o1 = out.(1) in
  let o2 = out.(2) in
  let o3 = out.(3) in
  out.(0) <- add_mod o0 (to_u128 (in0));
  out.(1) <- add_mod o1 (to_u128 (in1));
  out.(2) <- add_mod o2 (to_u128 (in2));
  out.(3) <- add_mod o3 (to_u128 (in3))

assume val mul_wide: a: uint_t U64 -> a: uint_t U64 -> Tot (uint_t U128)

(* )
val felem_scalar: out:felem -> scalar:uint32 ->
  Stack unit
    (requires (fun h -> live h out))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 out h0 h1))

let felem_scalar out scalar =
  let o0 = out.(0) in
  let o1 = out.(1) in
  let o2 = out.(2) in
  let o3 = out.(3) in
	let o0 = to_u64 o0 in
	let o1 = to_u64 o1 in
	let o2 = to_u64 o2 in
	let o3 = to_u64 o3 in
  out.(0) <- mul_wide o0 scalar;
  out.(1) <- mul_wide o1 scalar;
  out.(2) <- mul_wide o2 scalar;
  out.(3) <- mul_wide o3 scalar  

*)

val longfelem_scalar: out:longfelem -> scalar:uint64 ->
  Stack unit
    (requires (fun h -> live h out ))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 out h0 h1))

let longfelem_scalar out scalar =
  let o0 = out.(0) in
  let o1 = out.(1) in
  let o2 = out.(2) in
  let o3 = out.(3) in
  let o4 = out.(4) in
  let o5 = out.(5) in
  let o6 = out.(6) in
  let o7 = out.(7) in
  let o0 = to_u64 o0 in
  let o1 = to_u64 o1 in
  let o2 = to_u64 o2 in
  let o3 = to_u64 o3 in
  let o4 = to_u64 o4 in
  let o5 = to_u64 o5 in
  let o6 = to_u64 o6 in
  let o7 = to_u64 o7 in
  out.(0) <- mul_wide o0 scalar;
  out.(1) <- mul_wide o1 scalar;
  out.(2) <- mul_wide o2 scalar;
  out.(3) <- mul_wide o3 scalar;
  out.(4) <- mul_wide o4 scalar;
  out.(5) <- mul_wide o5 scalar;
  out.(6) <- mul_wide o6 scalar;
  out.(7) <- mul_wide o7 scalar

(*)
val load128: high: (uint_t U64) -> low: (uint_t U64) -> 
    Pure (uint_t U128) (requires True) 
    (ensures (fun b ->uint_v b = pow2 64 * uint_v high + uint_v low ))

let load128 high low = 
    let high = to_u128(high) in 
    let shift = u32(64) in 
    let hs = shift_left high shift in 
    	assert (uint_v hs = pow2 64 * uint_v high); 
    let ls = to_u128(low) in 
    	assert(uint_v ls = uint_v low);
    let result = logor hs ls in 
    	assert(uint_v (logor hs ls) = uint_v hs + uint_v ls);
    	assume (uint_v result = pow2 64 * uint_v high + uint_v low);
    result
(*)
let two105m41m9 = load128 (u64(0x1ffffffffff)) (u64(0xfffffdfffffffe00))
let two105      = load128 (u64(0x30000000000)) (u64(0x0))
let two105m41p9 = load128 (u64(0x1ffffffffff)) (u64(0xfffffe0000000200))

let two107m43m11 = load128 (u64(0x7ffffffffff)) (u64(0xfffff7fffffff800))
let two107       = load128 (u64(0x80000000000)) (u64(0x0))
let two107m43p11 = load128 (u64(0x7ffffffffff)) (u64(0xfffff80000000800))

let two64m0     =  to_u128 (u64(0xffffffffffffffff))
let two110p32m0 = load128 (u64(0x400000000000)) (u64(0x00000000ffffffff))
let two64m46    = to_u128 (u64(0xffffc00000000000))
let two64m32    = to_u128 (u64(0xffffffff00000000))

let two70m8p6     = load128 (u64(0x3f)) (u64(0xffffffffffffff40))
let two70p40      = load128 (u64(0x40)) (u64(0x0000010000000000))
let two70         = load128  (u64(0x40)) (u64(0x0000010000000000))
let two70m40m38p6 = load128 (u64(0x3f)) (u64(0xfffffec000000040))
let two70m6       = load128 (u64(0x3f)) (u64(0xffffffffffffffc0))

let two100m36m4 = load128 (u64(0xfffffffff)) (u64(0xffffffeffffffff0))
let two100      = load128 (u64(0x1000000000)) (u64(0x0))
let two100m36p4 = load128 (u64(0xfffffffff)) (u64(0xfffffff000000010))

module P256.Lib 


open FStar.Mul
open Spec.Lib.IntTypes
open Spec.Lib
open Spec.Lib.IntSeq


val load64_le: _in: intseq U8 8 -> Tot (uint_t U64)
let load64_le _in =
	let in0 = uint_to_nat_(index_ _in 0) in  
	let in1 = uint_to_nat_(index_ _in 1) in 
	let in2 = uint_to_nat_(index_ _in 2) in 
	let in3 = uint_to_nat_(index_ _in 3) in 
	let in4 = uint_to_nat_(index_ _in 4) in 
	let in5 = uint_to_nat_(index_ _in 5) in 
	let in6 = uint_to_nat_(index_ _in 6) in 
	let in7 = uint_to_nat_(index_ _in 7) in 
	let sum = (pow2 0 * in0 + pow2 8 * in1 + 
		pow2 16 * in2  + pow2 24 * in3  + pow2 32 * in4  + 
		pow2 40 * in5  + pow2 48 * in6 + pow2 56 * in7)  in 
	u64 sum

(*)
val test: unit -> Tot (uint_t U8)
*)
val mod: _in: uint_t U64 -> Tot (uint_t U8)
let mod _in = 
	let mask = u64(255) in 
	u8(logand _in mask)

val shift_mod: _in: uint_t U64->  shift: uint_t U64  -> Tot (uint_t U8)
let shift_mod _in shift = 
	let _in = shift_right _in shift in mod _in

assume val upd8: s: intseq U8 32 -> input: intseq U8 8 -> Tot (intseq U8 32)
assume val store64_le: input: uint_t U64 -> Tot (intseq U8 8)


(*)
let to_uint8 _in shift = shift_mod _in shift

let to_uint88 _in shift = 
	let s = create_ 8 (mod _in) in 
	let rec loop _in shift s = 
		if (shift < u64(8)) then  
			upd_ s shift (to_uint8 _in shift)	
		else
			s 
	in loop _in u64(1) s
				
				
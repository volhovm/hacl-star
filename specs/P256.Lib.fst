module P256.Lib 


open FStar.Mul
open Spec.Lib.IntTypes
open Spec.Lib
open Spec.Lib.IntSeq


assume val load64_le: _in: intseq U8 8 -> Tot (uint_t U64)
assume val mod: _in: uint_t U64 -> Tot (uint_t U8)
assume val shift_mod: _in: uint_t U64->  shift: uint_t U64  -> Tot (uint_t U8)
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
				
				
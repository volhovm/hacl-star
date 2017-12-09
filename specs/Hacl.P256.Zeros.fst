module Hacl.P256.Zeros

open FStar.Mul

open FStar.HyperStack
open FStar.HyperStack.ST

open Spec.Lib
open Spec.Lib.IntBuf
open Spec.Lib.IntTypes
open Spec.Lib.IntSeq.Lemmas

open P256.S

module Buffer = Spec.Lib.IntBuf


val load128: high: (uint_t U64) -> low: (uint_t U64) -> Pure (uint_t U128)
	(requires True)
    (ensures 
    	(fun b -> ((uint_v b) = pow2 64 * (uint_v high) + (uint_v low )))
    )

let load128 high low = 
    let high = to_u128(high) in 
    let shift = u32(64) in 
    let hs = shift_left high shift in  
    let ls = to_u128(low) in 
    let result = logor hs ls in 
    assume (uint_v result = pow2 64* uint_v high + uint_v low);
    result

let two105m41m9 = load128 (u64(0x1ffffffffff)) (u64(0xfffffdfffffffe00))
let two105      = load128 (u64(0x20000000000)) (u64(0x0))
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

val zero105: unit -> Stack felem
  (requires (fun h -> True))
  (ensures (fun h0 z h1 ->  creates1 z h0 h1 /\ preserves_live h0 h1 /\
  	(let s = as_lseq z h1 in 
  	let s0 = Spec.Lib.IntSeq.index s 0 in 
  	let s1 = Spec.Lib.IntSeq.index s 1 in 
  	let s2 = Spec.Lib.IntSeq.index s 2 in 
  	let s3 = Spec.Lib.IntSeq.index s 3 in 
  	s0 == two105m41m9 /\  s1 == two105 /\ s2 == two105m41p9 /\ s3 == two105m41p9
  )))

let zero105 () = 
	let s = create_felem() in 
	upd s 0 two105m41m9;
	upd s 1 two105;
	upd s 2 two105m41p9;
	upd s 3 two105m41p9;
	s

val zero105_2: f: felem -> Stack unit
	(requires (fun h -> live h f))
	(ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 f h0 h1 /\ 
	  	(let s = as_lseq f h1 in 
	  		let s0 = Spec.Lib.IntSeq.index s 0 in 
	  		let s1 = Spec.Lib.IntSeq.index s 1 in 
	  		let s2 = Spec.Lib.IntSeq.index s 2 in 
	  		let s3 = Spec.Lib.IntSeq.index s 3 in 
	  		s0 == two105m41m9 /\  s1 == two105 /\ s2 == two105m41p9 /\ s3 == two105m41p9
		))
	)

let zero105_2 f = 
	upd f 0 two105m41m9;
	upd f 1 two105;
	upd f 2 two105m41p9;
	upd f 3 two105m41p9

val zero107: unit -> Stack felem
  (requires (fun h -> True))
  (ensures (fun h0 z h1 -> creates1 z h0 h1 /\ preserves_live h0 h1 /\ 
  		(let s = as_lseq z h1 in 
	  		let s0 = Spec.Lib.IntSeq.index s 0 in 
	  		let s1 = Spec.Lib.IntSeq.index s 1 in 
	  		let s2 = Spec.Lib.IntSeq.index s 2 in 
	  		let s3 = Spec.Lib.IntSeq.index s 3 in 
	  		s0 == two107m43m11 /\  s1 == two107 /\ s2 == two107m43p11 /\ s3 == two107m43p11
		)



  ))

let zero107 () = 
	let s = create_felem() in 
	upd s 0 two107m43m11;
	upd s 1 two107;
	upd s 2 two107m43p11;
	upd s 3 two107m43p11;
	s

val zero107_2: f: felem -> Stack unit
	(requires (fun h -> live h f))
	(ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 f h0 h1 /\ 
	  	(let s = as_lseq f h1 in 
	  		let s0 = Spec.Lib.IntSeq.index s 0 in 
	  		let s1 = Spec.Lib.IntSeq.index s 1 in 
	  		let s2 = Spec.Lib.IntSeq.index s 2 in 
	  		let s3 = Spec.Lib.IntSeq.index s 3 in 
	  		s0 == two107m43m11 /\  s1 == two107 /\ s2 == two107m43p11 /\ s3 == two107m43p11
		))
	)

let zero107_2 f = 
	upd f 0 two107m43m11;
	upd f 1 two107;
	upd f 2 two107m43p11;
	upd f 3 two107m43p11



val zero110: unit -> Stack felem
  (requires (fun h -> True))
  (ensures (fun h0 z h1 -> creates1 z h0 h1 /\ preserves_live h0 h1))
 
let zero110 () = createL [two64m0; two110p32m0; two64m46; two64m32]

val zero100: unit -> Stack felem
  (requires (fun h -> True))
  (ensures (fun h0 z h1 -> creates1 z h0 h1 /\ preserves_live h0 h1))

let zero100 () = createL [two100m36m4; two100; two100m36p4; two100m36p4]



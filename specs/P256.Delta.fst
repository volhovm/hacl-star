val felem_shrink: input: felem -> output: smallfelem -> Tot (smallfelem)

let felem_shrink input output = 
    let tmp = create_felem() in 
    let a = u64(0) in let b = u64(0) in let mask = u64(0) in 
(* ! *)   let high = u64(0) in let low = u64(0) in 
    let kPrime3Test = 0x7fffffff00000001uL in 
    let zero110 =  zero110() in 
    let zero110_0 = index zero110 0 in 
    let zero110_1 = index zero110 1 in 
    let zero110_2 = index zero110 2 in 
    let zero110_3 = index zero110 3 in 
    let in0 = index input 0 in 
    let in1 = index input 1 in 
    let in2 = index input 2 in 
    let in3 = index input 3 in 
    let kPrime_0 = index kPrime 0 in 
    let kPrime_1 = index kPrime 1 in 
    let kPrime_2 = index kPrime 2 in 
    let kPrime_3 = index kPrime 3 in (*)
    let tmp = upd_ tmp 3 (add (add zero110_3 in3) (to_u128 #U64 (to_u64 #U128 (shift_right in2 64)))) in 
    let tmp = upd_ tmp 2 (add zero110_2 (to_u64(in2))) in 
    let tmp = upd_ tmp 0 (add zero110_0 in0) in 
    let tmp = upd_ tmp 1 (add zero110_1 in1) in 
    let a = shift_right (index tmp 3) (u32(64)) in 
    let tmp = upd_ tmp 3 (to_u128 #U64 (to_u64 #U128 (index tmp 3))) in 
    let tmp = upd_ tmp 3 (Spec.Lib.IntTypes.sub (index tmp 3) a) in 
    let tmp = upd_ tmp 3 (shift_left (to_u128(a)) 32) in *)

    let i0,i1,i2, i3 = get4 tmp in 
    let b = a in 
    let a = shift_right i3 64 in 
    let b = add a b in 
    let tmp = upd_ tmp 3 (to_u128 #U64 (to_u64 #U128(i3))) in 
    let tmp = upd_ tmp 3 (Spec.Lib.IntTypes.sub (index tmp 3) a) in 
    let tmp = upd_ tmp 3 (shift_left (to_u128(a)) 32) in 
    let tmp = upd_ tmp 0 (add i0 b) in 
    let tmp = upd_ tmp 1 (Spec.Lib.IntTypes.sub i1 (shift_left (to_u128 b) 32)) in 
    let high = shift_right (index tmp 3) 64 in 
    let high = shift_left high 63 in 
    let high = shift_right high 63 in 
    let low = (index tmp 3) in 
    let mask = shift_right low 63 in 
    let low = logand low bottom63bits in 
    let low = Spec.Lib.IntTypes.sub low kPrime3Test in 
    let low = lognot low in 
    let low = shift_right low 63 in 
    let mask = logor(logand mask low) high in 
    let i0, i1, i2, i3 = get4 tmp in
    let tmp = upd_ tmp 0 (Spec.Lib.IntTypes.sub (i0) (logand mask (to_u128(kPrime_0)))) in 
    let tmp = upd_ tmp 1 (Spec.Lib.IntTypes.sub (i1) (logand mask (to_u128(kPrime_1)))) in 
    let tmp = upd_ tmp 2 (Spec.Lib.IntTypes.sub (i2) (logand mask (to_u128(kPrime_3)))) in 
    let i0, i1, i2, i3 = get4 tmp in
    let tmp = upd_ tmp 1 (Spec.Lib.IntTypes.sub i1 (to_u64( shift_right i0 64))) in 
    let tmp = upd_ tmp 0 (to_u64 i0) in 
    let tmp = upd_ tmp 2 (Spec.Lib.IntTypes.sub i2 (to_u64( shift_right (index tmp 1) 64))) in 
    let tmp = upd_ tmp 0 (to_u64 ((index tmp 1))) in 
    let tmp = upd_ tmp 3 (Spec.Lib.IntTypes.sub (index tmp 3) (to_u64( shift_right (index tmp 2) 64))) in 
    let tmp = upd_ tmp 0 (to_u64 ((index tmp 2))) in 
    let s = create_smallfelem () in 

    let i0, i1, i2, i3 = get4 tmp in
    let s = upd_ s 0 (to_u64 i0) in 
    let s = upd_ s 1 (to_u64 i1) in 
    let s = upd_ s 2 (to_u64 i2) in 
    let s = upd_ s 3 (to_u64 i3) in 
    s
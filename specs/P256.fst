module P256

open FStar.Mul
open Spec.Lib.IntTypes

open Spec.Lib
open Spec.Lib.IntSeq

open P256.Lib

module Seq = Spec.Lib.IntSeq

private let s64 = FStar.Int64.t


inline_for_extraction
unfold
private let limb = Spec.Lib.IntTypes.U128

private let felem_bytearray = s: intseq U8 32

let nlimbs = 4

private let felem = s: intseq limb nlimbs
private let longfelem = s: intseq limb (nlimbs * 2)
private let smallfelem = s: intseq U64 (nlimbs)

let kPrime :intseq U64 4 = Seq.createL [0xffffffffffffffffUL; 0xffffffffUL; 0x0UL; 0xffffffff00000001UL]

let bottom63bits = 0x7fffffffffffffffUL

val create_felem: unit -> Tot (felem)
let create_felem () = 
	let zero = u128(0) in create_ zero nlimbs

val create_smallfelem: unit -> Tot (smallfelem)
let create_smallfelem () = 
	let zero = u64(0) in create_ zero nlimbs

val create_longfelem: unit -> Tot (longfelem)
let create_longfelem () = 
	let zero = u128(0) in create_ zero (nlimbs*2)


(*
 * bin32_to_felem takes a little-endian byte array and converts it into felem
 * form. This assumes that the CPU is little-endian.
 *)

val bin32_to_felem: _in: intseq U8 32 -> Tot (felem)

let bin32_to_felem _in = 
	let in0 = slice _in 0 8 in 
	let in1 = slice _in 8 16 in 
	let in2 = slice _in 16 24 in 
	let in3 = slice _in 24 32 in 
	let o0 = to_u128(load64_le in0) in 
	let o1 = to_u128(load64_le in1) in 
	let o2 = to_u128(load64_le in2) in 
	let o3 = to_u128(load64_le in3) in 
	let s = create_felem () in 
	let s = upd_ s 0 o0 in 
	let s = upd_ s 1 o1 in 
	let s = upd_ s 2 o2 in 
	let s = upd_ s 3 o3 in 
	s

(*
 * smallfelem_to_bin32 takes a smallfelem and serialises into a little
 * endian, 32 byte array. This assumes that the CPU is little-endian.
 *
static void smallfelem_to_bin32(u8 out[32], const smallfelem in)
{
    *((u64 *&out[0]) = in[0];
    *((u64 *&out[8]) = in[1];
    *((u64 *&out[16]) = in[2];
    *((u64 *&out[24]) = in[3];
}
*)

val smallfelem_to_bin32: input: smallfelem -> Tot (intseq U8 32)

let smallfelem_to_bin32 input = 
	let zero = u8(0) in 
	let in0 = index input 0 in 
	let in1 = index input 1 in 
	let in2 = index input 2 in 
	let in3 = index	input 3 in 
	let output = create_ 32 zero in 
	let output = upd8 output (store64_le in0) in 
	let output = upd8 output (store64_le in1) in 
	let output = upd8 output (store64_le in2) in 
	let output = upd8 output (store64_le in3) in 
	output

(*
/* To preserve endianness when using BN_bn2bin and BN_bin2bn */
static void flip_endian(u8 *out, const u8 *in, unsigned len)
{
    unsigned i;
    for (i = 0; i < len; ++i)
        out[i] = in[len - 1 - i];
} *)

val flip_endian: len: (uint_t U32) ->  input: intseq U8 len -> Tot (intseq U8 len)

let flip_endian len input = 
	let zero = u8(0) in 
	let output = create_ len zero in
	let counter = 0 in 
	let f (counter:size_t{counter < len}) (output:intseq U8 len)  = 
		let toChange = index input counter  in 
		upd_ output counter toChange in 
	repeati len f output

(*static void smallfelem_one(smallfelem out)
{
    out[0] = 1;
    out[1] = 0;
    out[2] = 0;
    out[3] = 0;
}
 *)

val smallfelem_one : unit -> Tot (smallfelem)

let smallfelem_one () = 
	let one = u64(1) in 
	let s = create_smallfelem () in 
	let s = upd_ s 0 one in s
(*)
static void smallfelem_assign(smallfelem out, const smallfelem in)
{
    out[0] = in[0];
    out[1] = in[1];
    out[2] = in[2];
    out[3] = in[3];
}
*)

val smallfelem_assign: input: smallfelem -> Tot (smallfelem)

let smallfelem_assign input = 
	let in0 = index input 0 in 
	let in1 = index input 1 in 
	let in2 = index	input 2 in 
	let in3 = index input 3 in 
	let s = create_smallfelem () in 
	let s = upd_ s 0 in0 in 
	let s = upd_ s 1 in1 in 
	let s = upd_ s 2 in2 in 
	let s = upd_ s 3 in3 in 
	s

(*static void felem_assign(felem out, const felem in)
{
    out[0] = in[0];
    out[1] = in[1];
    out[2] = in[2];
    out[3] = in[3];
} *)   


val felem_assign: input: felem -> Tot (felem)

let felem_assign input = 
    let in0 = index input 0 in 
    let in1 = index input 1 in 
    let in2 = index input 2 in 
    let in3 = index input 3 in 
    let s = create_felem() in 
    let s = upd_ s 0 in0 in 
    let s = upd_ s 1 in1 in 
    let s = upd_ s 2 in2 in 
    let s = upd_ s 3 in3 in 
    s


(*) felem_sum sets out = out + in. */
static void felem_sum(felem out, const felem in)
{
    out[0] += in[0];
    out[1] += in[1];
    out[2] += in[2];
    out[3] += in[3];
}
*)

(* non-carry addition of felem's *)
(* #include <stdio.h>
#include <limits.h>

int main()
{
    unsigned int a = UINT_MAX ;
    unsigned int b = 1000 + a;
    printf("%d \n",  b);

    unsigned int c = (1000 + a) % a;
    printf("%i \n", c);

    return 0;
}

returns the same. 
 *)
val felem_sum: input: felem-> output: felem -> Tot felem

let felem_sum input output = 
    let in0 = index input 0 in 
    let in1 = index input 1 in 
    let in2 = index input 2 in 
    let in3 = index input 3 in 
    let o0 = index output 0 in 
    let o1 = index output 1 in 
    let o2 = index output 2 in 
    let o3 = index output 3 in 
    let s = create_felem() in 
    let s = upd_ s 0 (add_mod in0 o0) in 
    let s = upd_ s 1 (add_mod in1 o1) in 
    let s = upd_ s 2 (add_mod in2 o2) in 
    let s = upd_ s 3 (add_mod in3 o3) in 
    s

(*)
static void felem_small_sum(felem out, const smallfelem in)
{
    out[0] += in[0];
    out[1] += in[1];
    out[2] += in[2];
    out[3] += in[3];
}
*)

val felem_small_sum: input: smallfelem -> output: felem -> Tot (felem)

let felem_small_sum input output = 
    let in0 = to_u128(index input 0) in 
    let in1 = to_u128(index input 1) in 
    let in2 = to_u128(index input 2) in 
    let in3 = to_u128(index input 3) in 
    let o0 = index output 0 in 
    let o1 = index output 1 in 
    let o2 = index output 2 in 
    let o3 = index output 3 in 
    let s = create_felem() in 
    let s = upd_ s 0 (add_mod in0 o0) in 
    let s = upd_ s 1 (add_mod in1 o1) in 
    let s = upd_ s 2 (add_mod in2 o2) in 
    let s = upd_ s 3 (add_mod in3 o3) in 
    s

(*)
static void felem_scalar(felem out, const u64 scalar)
{
    out[0] *= scalar;
    out[1] *= scalar;
    out[2] *= scalar;
    out[3] *= scalar;
}
*)

(* 
    mod = 2^8
    aprime = 255 
    a = 15 
    b = 15

    c = (a <<15)% mod
    c, (aprime * b % mod)
*) 

(*)

    mod = 2^32

    number = 2^32 - 1
    scalar = 7

    a = ((number) + (number <<1 % mod) + (number <<2 % mod)) % mod
    b = (number * scalar ) % mod

    a, b 


*)

assume val mul_wide: a: uint_t U64 -> a: uint_t U64 -> Tot (uint_t U128)

val felem_scalar: scalar: (uint_t U64) -> output: felem -> Tot (felem)

let felem_scalar scalar output = 
    let o0 = index output 0 in 
    let o1 = index output 1 in 
    let o2 = index output 2 in 
    let o3 = index output 3 in 

    let o0 = to_u64(o0) in 
    let o1 = to_u64(o1) in 
    let o2 = to_u64(o2) in 
    let o3 = to_u64(o3) in 

    let s = create_felem() in 

    (*)
    let s = upd_ s 0 (shift_left o0 scalar) in 
    let s = upd_ s 1 (shift_left o1 scalar) in 
    let s = upd_ s 2 (shift_left o2 scalar) in 
    let s = upd_ s 3 (shift_left o3 scalar) in 

    *)
    (*)
    let s = upd_ s 0 (mul_wide o0 scalar) in 
    let s = upd_ s 1 (mul_wide o1 scalar) in 
    let s = upd_ s 2 (mul_wide o2 scalar) in 
    let s = upd_ s 3 (mul_wide o3 scalar) in 
    *)

    s

(*static void longfelem_scalar(longfelem out, const u64 scalar)
{
    out[0] *= scalar;
    out[1] *= scalar;
    out[2] *= scalar;
    out[3] *= scalar;
    out[4] *= scalar;
    out[5] *= scalar;
    out[6] *= scalar;
    out[7] *= scalar;
}
*)

val longfelem_scalar: scalar: (uint_t U64) ->output: longfelem -> Tot longfelem

let longfelem_scalar scalar output = 
    let o0 = index output 0 in 
    let o1 = index output 1 in 
    let o2 = index output 2 in 
    let o3 = index output 3 in 
    let o4 = index output 4 in 
    let o5 = index output 5 in 
    let o6 = index output 6 in 
    let o7 = index output 7 in 

    let o0 = to_u64(o0) in 
    let o1 = to_u64(o1) in 
    let o2 = to_u64(o2) in 
    let o3 = to_u64(o3) in 
    let o4 = to_u64(o4) in 
    let o5 = to_u64(o5) in 
    let o6 = to_u64(o6) in 
    let o7 = to_u64(o7) in 

    let s = create_longfelem() in 
    let s = upd_ s 0 (mul_wide o0 scalar) in 
    let s = upd_ s 1 (mul_wide o1 scalar) in 
    let s = upd_ s 2 (mul_wide o2 scalar) in 
    let s = upd_ s 3 (mul_wide o3 scalar) in 
    let s = upd_ s 4 (mul_wide o4 scalar) in 
    let s = upd_ s 5 (mul_wide o5 scalar) in 
    let s = upd_ s 6 (mul_wide o6 scalar) in 
    let s = upd_ s 7 (mul_wide o7 scalar) in 
    s

(*val load128: high:UInt64.t -> low:UInt64.t -> Tot (z:UInt128.t{UInt128.v z = pow2 64 * UInt64.v high
  + UInt64.v low})
let load128 h l =
  let open FStar.UInt128 in
  let hs = uint64_to_uint128 h <<^ 64ul in
  let ls = uint64_to_uint128 l in
  Math.Lemmas.modulo_lemma (UInt64.v h * pow2 64) (pow2 128);
  UInt.logor_disjoint #128 (v hs) (v ls) 64;
hs |^ ls *)

val load128: high: (uint_t U64) -> low: (uint_t U64) -> 
    Pure (uint_t U128) (requires True) 
    (ensures (fun b ->uint_v b = pow2 64 * uint_v high + uint_v low ))

let load128 high low = 
    let high = u128(high) in 
    let shift = u32(64) in 
    let hs = shift_left high shift in 
    let ls = u128(low) in 
    let result = logor hs ls in 
    result

let two105m41m9 = load128 0x1ffffffffffuL 0xfffffdfffffffe00uL
let two105      = load128 0x30000000000uL 0x0uL
let two105m41p9 = load128 0x1ffffffffffuL 0xfffffe0000000200uL

let two107m43m11 = load128 0x7ffffffffffuL 0xfffff7fffffff800uL
let two107       = load128 0x80000000000uL 0x0uL
let two107m43p11 = load128 0x7ffffffffffuL 0xfffff80000000800uL

let two64m0     =  to_u128 #U64 (0xffffffffffffffffuL)
let two110p32m0 = load128 0x400000000000uL 0x00000000ffffffffuL
let two64m46    = to_u128 #U64 (0xffffc00000000000uL)
let two64m32    = to_u128 #U64 (0xffffffff00000000uL)

let two70m8p6     = load128 0x3fuL 0xffffffffffffff40uL
let two70p40      = load128 0x40uL 0x0000010000000000uL
let two70         = load128  0x40uL 0x0000010000000000uL
let two70m40m38p6 = load128 0x3fuL 0xfffffec000000040uL
let two70m6       = load128 0x3fuL 0xffffffffffffffc0uL

let two100m36m4 = load128 0xfffffffffuL 0xffffffeffffffff0uL
let two100      = load128 0x1000000000uL 0x0uL
let two100m36p4 = load128 0xfffffffffuL 0xfffffff000000010uL


(* )
static const felem zero105 =
{ two105m41m9, two105, two105m41p9, two105m41p9 };*)

val zero105 : unit -> Tot (felem)

let zero105 () = 
    let s = create_felem() in 
    let s = upd_ s 0 two105m41p9 in 
    let s = upd_ s 1 two105 in 
    let s = upd_ s 2 two105m41p9 in 
    let s = upd_ s 3 two105m41p9 in 
    s

(* static const felem zero107 =
{ two107m43m11, two107, two107m43p11, two107m43p11 }; *)
val zero107: unit -> Tot (felem)
let zero107 () = 
    let s = create_felem() in 
    let s = upd_ s 0 two107m43m11 in 
    let s = upd_ s 1 two107 in 
    let s = upd_ s 2 two107m43p11 in 
    let s = upd_ s 3 two107m43p11 in 
    s
(*)
/* zero110 is 0 mod p */
static const felem zero110 = { two64m0, two110p32m0, two64m46, two64m32 };
*)

val zero110 : unit -> Tot (felem)
let zero110 ()  = 
    let s = create_felem() in 
    let s = upd_ s 0 two64m0 in 
    let s = upd_ s 1 two110p32m0 in 
    let s = upd_ s 2 two64m46 in 
    let s = upd_ s 3 two64m32 in 
    s

(*)
/*-
 * smallfelem_neg sets |out| to |-small|
 * On exit:
 *   out[i] < out[i] + 2^105
 */
static void smallfelem_neg(felem out, const smallfelem small)
{
    /* In order to prevent underflow, we subtract from 0 mod p. */
    out[0] = zero105[0] - small[0];
    out[1] = zero105[1] - small[1];
    out[2] = zero105[2] - small[2];
    out[3] = zero105[3] - small[3];
}
*)

val smallfelem_neg: small: smallfelem -> Tot felem

let smallfelem_neg small = 
    let zero105 = zero105() in 
    let zero105_0 = index zero105 0 in 
    let zero105_1 = index zero105 1 in 
    let zero105_2 = index zero105 2 in 
    let zero105_3 = index zero105 3 in 
    let small0 = index small 0 in 
    let small1 = index small 1 in 
    let small2 = index small 2 in 
    let small3 = index small 3 in
    let small0 = to_u128(small0) in  
    let small1 = to_u128(small1) in 
    let small2 = to_u128(small2) in 
    let small3 = to_u128(small3) in 
    let s = create_felem() in 
    let s = upd_ s 0 (Spec.Lib.IntTypes.sub zero105_0 small0) in 
    let s = upd_ s 1 (Spec.Lib.IntTypes.sub zero105_1 small1) in 
    let s = upd_ s 2 (Spec.Lib.IntTypes.sub zero105_2 small2) in 
    let s = upd_ s 3 (Spec.Lib.IntTypes.sub zero105_3 small3) in 
    s 

(*)
static void felem_diff(felem out, const felem in)
{
    /*
     * In order to prevent underflow, we add 0 mod p before subtracting.
     */
    out[0] += zero105[0];
    out[1] += zero105[1];
    out[2] += zero105[2];
    out[3] += zero105[3];

    out[0] -= in[0];
    out[1] -= in[1];
    out[2] -= in[2];
    out[3] -= in[3];
}
*)

val felem_diff: input: felem -> output: felem -> Tot (felem)

let felem_diff input output = 
    let zero105 = zero105() in 
    let zero105_0 = index zero105 0 in 
    let zero105_1 = index zero105 1 in 
    let zero105_2 = index zero105 2 in 
    let zero105_3 = index zero105 3 in 
    let o0 = index output 0 in 
    let o1 = index output 1 in 
    let o2 = index output 2 in 
    let o3 = index output 3 in 
    let i0 = index input 0 in 
    let i1 = index input 1 in 
    let i2 = index input 2 in 
    let i3 = index input 3 in 
    let o0 = add o0 zero105_0 in 
    let o1 = add o1 zero105_1 in 
    let o2 = add o2 zero105_2 in 
    let o3 = add o3 zero105_3 in 
    let s = create_felem() in 
    let s = upd_ s 0 (Spec.Lib.IntTypes.sub o0 i0) in 
    let s = upd_ s 1 (Spec.Lib.IntTypes.sub o1 i1) in
    let s = upd_ s 2 (Spec.Lib.IntTypes.sub o2 i2) in 
    let s = upd_ s 3 (Spec.Lib.IntTypes.sub o3 i3) in 
    s


(*/*-
 * An alternative felem_diff for larger inputs |in|
 * felem_diff_zero107 subtracts |in| from |out|
 * On entry:
 *   in[i] < 2^106
 * On exit:
 *   out[i] < out[i] + 2^107
 */
static void felem_diff_zero107(felem out, const felem in)
{
    /*
     * In order to prevent underflow, we add 0 mod p before subtracting.
     */
    out[0] += zero107[0];
    out[1] += zero107[1];
    out[2] += zero107[2];
    out[3] += zero107[3];

    out[0] -= in[0];
    out[1] -= in[1];
    out[2] -= in[2];
    out[3] -= in[3];
}
 *)

val felem_diff_zero107: input: felem -> output: felem -> Tot (felem)

let felem_diff_zero107 input output = 
    let zero107 = zero107() in 
    let zero107_0 = index zero107 0 in 
    let zero107_1 = index zero107 1 in 
    let zero107_2 = index zero107 2 in 
    let zero107_3 = index zero107 3 in 
    let o0 = index output 0 in 
    let o1 = index output 1 in 
    let o2 = index output 2 in 
    let o3 = index output 3 in 
    let i0 = index input 0 in 
    let i1 = index input 1 in 
    let i2 = index input 2 in 
    let i3 = index input 3 in 
    let o0 = add o0 zero107_0 in 
    let o1 = add o1 zero107_1 in 
    let o2 = add o2 zero107_2 in 
    let o3 = add o3 zero107_3 in 
    let s = create_felem() in 
    let s = upd_ s 0 (Spec.Lib.IntTypes.sub o0 i0) in 
    let s = upd_ s 1 (Spec.Lib.IntTypes.sub o1 i1) in
    let s = upd_ s 2 (Spec.Lib.IntTypes.sub o2 i2) in 
    let s = upd_ s 3 (Spec.Lib.IntTypes.sub o3 i3) in 
    s
(*)
/*-
 * longfelem_diff subtracts |in| from |out|
 * On entry:
 *   in[i] < 7*2^67
 * On exit:
 *   out[i] < out[i] + 2^70 + 2^40
 */
static void longfelem_diff(longfelem out, const longfelem in)
{
    static const limb two70m8p6 =
        (((limb) 1) << 70) - (((limb) 1) << 8) + (((limb) 1) << 6);
    static const limb two70p40 = (((limb) 1) << 70) + (((limb) 1) << 40);
    static const limb two70 = (((limb) 1) << 70);
    static const limb two70m40m38p6 =
        (((limb) 1) << 70) - (((limb) 1) << 40) - (((limb) 1) << 38) +
        (((limb) 1) << 6);
    static const limb two70m6 = (((limb) 1) << 70) - (((limb) 1) << 6);

    /* add 0 mod p to avoid underflow */
    out[0] += two70m8p6;
    out[1] += two70p40;
    out[2] += two70;
    out[3] += two70m40m38p6;
    out[4] += two70m6;
    out[5] += two70m6;
    out[6] += two70m6;
    out[7] += two70m6;

    /* in[i] < 7*2^67 < 2^70 - 2^40 - 2^38 + 2^6 */
    out[0] -= in[0];
    out[1] -= in[1];
    out[2] -= in[2];
    out[3] -= in[3];
    out[4] -= in[4];
    out[5] -= in[5];
    out[6] -= in[6];
    out[7] -= in[7];
}

*)

val longfelem_diff: input: longfelem -> output: longfelem -> Tot (longfelem)

let longfelem_diff input output = 
    let o0 = index output 0 in 
    let o1 = index output 1 in 
    let o2 = index output 2 in 
    let o3 = index output 3 in 
    let o4 = index output 4 in 
    let o5 = index output 5 in 
    let o6 = index output 6 in 
    let o7 = index output 7 in 
    let i0 = index input 0 in 
    let i1 = index input 1 in 
    let i2 = index input 2 in 
    let i3 = index input 3 in 
    let i4 = index input 4 in 
    let i5 = index input 5 in 
    let i6 = index input 6 in 
    let i7 = index input 7 in 
    let o0 = add o0 two70m8p6 in 
    let o1 = add o1 two70p40 in 
    let o2 = add o2 two70 in 
    let o3 = add o3 two70m40m38p6 in 
    let o4 = add o4 two70m6 in 
    let o5 = add o5 two70m6 in 
    let o6 = add o6 two70m6 in 
    let o7 = add o7 two70m6 in 
    let s = create_longfelem() in 
    let s = upd_ s 0 (Spec.Lib.IntTypes.sub o0 i0) in 
    let s = upd_ s 1 (Spec.Lib.IntTypes.sub o1 i1) in 
    let s = upd_ s 2 (Spec.Lib.IntTypes.sub o2 i2) in 
    let s = upd_ s 3 (Spec.Lib.IntTypes.sub o3 i3) in 
    let s = upd_ s 4 (Spec.Lib.IntTypes.sub o4 i4) in 
    let s = upd_ s 5 (Spec.Lib.IntTypes.sub o5 i5) in 
    let s = upd_ s 6 (Spec.Lib.IntTypes.sub o6 i6) in 
    let s = upd_ s 7 (Spec.Lib.IntTypes.sub o7 i7) in 
    s

(* /*-
 * felem_shrink converts an felem into a smallfelem. The result isn't quite
 * minimal as the value may be greater than p.
 *
 * On entry:
 *   in[i] < 2^109
 * On exit:
 *   out[i] < 2^64
 */

*)
(*)
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
    let kPrime_3 = index kPrime 3 in 
    let tmp = upd_ tmp 3 (add (add zero110_3 in3) (to_u128 #U64 (to_u64 #U128 (shift_right in2 64)))) in 
    let tmp = upd_ tmp 2 (add zero110_2 (to_u64(in2))) in 
    let tmp = upd_ tmp 0 (add zero110_0 in0) in 
    let tmp = upd_ tmp 1 (add zero110_1 in1) in 
    let a = shift_right (index tmp 3) (u32(64)) in 
    let tmp = upd_ tmp 3 (to_u128 #U64 (to_u64 #U128 (index tmp 3))) in 
    let tmp = upd_ tmp 3 (Spec.Lib.IntTypes.sub (index tmp 3) a) in 
    let tmp = upd_ tmp 3 (shift_left (to_u128(a)) 32) in 
    let b = a in 
    let a = shift_right (index tmp 3) 64 in 
    let b = add a b in 
    let tmp = upd_ tmp 3 (to_u128 #U64 (to_u64 #U128(index tmp 3))) in 
    let tmp = upd_ tmp 3 (Spec.Lib.IntTypes.sub (index tmp 3) a) in 
    let tmp = upd_ tmp 3 (shift_left (to_u128(a)) 32) in 
    let tmp = upd_ tmp 0 (add (index tmp 0) b) in 
    let tmp = upd_ tmp 1 (Spec.Lib.IntTypes.sub (index tmp 1) (shift_left (to_u128 b) 32)) in 
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
    let tmp = upd_ tmp 0 (Spec.Lib.IntTypes.sub (index tmp 0) (logand mask (to_u128(kPrime_0)))) in 
    let tmp = upd_ tmp 1 (Spec.Lib.IntTypes.sub (index tmp 1) (logand mask (to_u128(kPrime_1)))) in 
    let tmp = upd_ tmp 2 (Spec.Lib.IntTypes.sub (index tmp 2) (logand mask (to_u128(kPrime_3)))) in 
    let tmp = upd_ tmp 1 (Spec.Lib.IntTypes.sub (index tmp 1) (to_u64( shift_right (index tmp 0) 64))) in 
    let tmp = upd_ tmp 0 (to_u64 ((index tmp 0))) in 
    let tmp = upd_ tmp 2 (Spec.Lib.IntTypes.sub (index tmp 2) (to_u64( shift_right (index tmp 1) 64))) in 
    let tmp = upd_ tmp 0 (to_u64 ((index tmp 1))) in 
    let tmp = upd_ tmp 3 (Spec.Lib.IntTypes.sub (index tmp 3) (to_u64( shift_right (index tmp 2) 64))) in 
    let tmp = upd_ tmp 0 (to_u64 ((index tmp 2))) in 
    let s = create_smallfelem () in 
    let s = upd_ s 0 (to_u64(index tmp 0)) in 
    let s = upd_ s 1 (to_u64(index tmp 1)) in 
    let s = upd_ s 2 (to_u64(index tmp 2)) in 
    let s = upd_ s 3 (to_u64(index tmp 3)) in 
    s
*)
(*/* smallfelem_expand converts a smallfelem to an felem */
static void smallfelem_expand(felem out, const smallfelem in)
{
    out[0] = in[0];
    out[1] = in[1];
    out[2] = in[2];
    out[3] = in[3];
} *)

val smallfelem_expand: input: smallfelem -> Tot felem
let smallfelem_expand input = 
    let s = create_felem() in 
    let in0 = index input 0 in 
    let in1 = index input 1 in 
    let in2 = index input 2 in 
    let in3 = index input 3 in 
    let s = upd_ s 0 (to_u128 in0) in 
    let s = upd_ s 1 (to_u128 in1) in 
    let s = upd_ s 2 (to_u128 in2) in 
    let s = upd_ s 3 (to_u128 in3) in 
    s

(*-
 * smallfelem_square sets |out| = |small|^2
 * On entry:
 *   small[i] < 2^64
 * On exit:
 *   out[i] < 7 * 2^64 < 2^67
 */
static void smallfelem_square(longfelem out, const smallfelem small)
{
    limb a;
    u64 high, low;

    a = ((uint128_t) small[0]) * small[0];
    low = a;
    high = a >> 64;
    out[0] = low;
    out[1] = high;

    a = ((uint128_t) small[0]) * small[1];
    low = a;
    high = a >> 64;
    out[1] += low;
    out[1] += low;
    out[2] = high;

    a = ((uint128_t) small[0]) * small[2];
    low = a;
    high = a >> 64;
    out[2] += low;
    out[2] *= 2;
    out[3] = high;

    a = ((uint128_t) small[0]) * small[3];
    low = a;
    high = a >> 64;
    out[3] += low;
    out[4] = high;

    a = ((uint128_t) small[1]) * small[2];
    low = a;
    high = a >> 64;
    out[3] += low;
    out[3] *= 2;
    out[4] += high;

    a = ((uint128_t) small[1]) * small[1];
    low = a;
    high = a >> 64;
    out[2] += low;
    out[3] += high;

    a = ((uint128_t) small[1]) * small[3];
    low = a;
    high = a >> 64;
    out[4] += low;
    out[4] *= 2;
    out[5] = high;

    a = ((uint128_t) small[2]) * small[3];
    low = a;
    high = a >> 64;
    out[5] += low;
    out[5] *= 2;
    out[6] = high;
    out[6] += high;

    a = ((uint128_t) small[2]) * small[2];
    low = a;
    high = a >> 64;
    out[4] += low;
    out[5] += high;

    a = ((uint128_t) small[3]) * small[3];
    low = a;
    high = a >> 64;
    out[6] += low;
    out[7] = high;
}
*)

val smallfelem_square : small: smallfelem -> Tot longfelem

let smallfelem_square small = 
    let out = create_felem() in 
    let a = u128(0) in 
    let high = u64(0) in let low = u64(0) in 
    let small0 = index small 0 in 
    let small1 = index small 1 in 
    let small2 = index small 2 in 
    let small3 = index small 3 in 
(* ? *)  
    let a = mul_wide small0 small0 in 
    let low = a in 
    let high = shift_right a 64 in 
    let out = upd_ out 0 low in 
    let out = upd_ out 1 high in 
    
    let a = mul_wide small0 small1 in 
    let low = a in 
    let high = shift_right a 64 in
    let out1 = index out 1 in 
    let out = upd_ out 1 (add out1 low) in 
    let out1 = index out 1 in 
    let out = upd_ out 1 (add out1 low) in 
    let out = upd_ out 2 high in 

    let a = mul_wide small0 small2 in 
    let low = a in 
    let high = shift_right a 64 in 
    let out2 = index out 2 in 
    let out = upd_ out 2 (add out2 low) in 
    let out2 = index out 2 in 
    let out = upd_ out 2 (shift_left out2 2) in 
    let out = upd_ out 3 high in 

    let a = mul_wide small0 small3 in 
    let low = a in 
    let high = shift_right a 64 in
    let out3 = index out 3 in 
    let out = upd_ out 3 (add out3 low) in 
    let out = upd_ out 4 high in 

    let a = mul_wide small1 small2 in 
    let low = a in 
    let high = shift_right a 64 in
    let out3 = index out 3 in 
    let out = upd_ out 3 (add out3 low) in 
    let out3 = index out 3 in 
    let out = upd_ out 3 (shift_left out3 2) in 
    let out4 = index out 4 in 
    let out = upd_ out 4 (add out4 high) in 

    let a = mul_wide small1 small1 in 
    let low = a in 
    let high = shift_right a 64 in
    let out2 = index out 2 in 
    let out = upd_ out 2 (add out2 low) in 
    let out3 = index out 3 in 
    let out = upd_ out 4 (add out3 high) in 

     let a = mul_wide small1 small3 in 
    let low = a in 
    let high = shift_right a 64 in
    let out4 = index out 4 in 
    let out = upd_ out 4 (add out4 low) in 
    let out4 = index out 4 in 
    let out = upd_ out 4 (shift_left out4 2) in 
    let out = upd_ out 5 high    in 

    let a = mul_wide small2 small3 in 
    let low = a in 
    let high = shift_right a 64 in
    let out5 = index out 5 in 
    let out = upd_ out 5 (add out5 low) in 
    let out5 = index out 5 in 
    let out = upd_ out 5 (shift_left out5 2) in 
    let out = upd_ out 6 (add high high) in 

    let a = mul_wide small2 small2 in 
    let low = a in 
    let high = shift_right a 64 in
    let out4 = index out 4 in 
    let out = upd_ out 4 (add out4 low) in 
    let out5 = index out 5 in 
    let out = upd_ out 5 (add out5 high) in 

    let a = mul_wide small3 small3 in 
    let low = a in 
    let high = shift_right a 64 in
    let out6 = index out 6 in 
    let out6 = upd_ out 6 (add out6 low) in 
    let out = upd_ out 7 high in out















val point_double: x_in: felem -> y_in: felem -> z_in: felem -> Tot (tuple3 (x_out: felem) (y_out: felem) (z_out:felem))

module Hacl.Spec.P256.Core

open Lib.IntTypes
open FStar.Math.Lemmas
open FStar.Math.Lib
open Hacl.Spec.Curve25519.Field64.Definition
open Hacl.Spec.P256.Definitions
open Hacl.Spec.Curve25519.Field64.Core
open Hacl.Spec.P256.Lemmas

open FStar.Mul

inline_for_extraction noextract
val eq_u64:a:uint64 -> b:uint64 -> Tot (r: bool {if uint_v a = uint_v b then r == true else r == false})

val eq_0_u64: a: uint64 -> Tot (r: bool {if uint_v a = 0 then r == true else r == false})


val felem_add: arg1: felem4 {as_nat4 arg1 < prime} -> arg2: felem4{as_nat4 arg2 < prime} -> Tot (r : felem4 {as_nat4 r == (as_nat4 arg1 + as_nat4 arg2) % prime})

val felem_sub: arg1: felem4 {as_nat4 arg1 < prime} -> arg2: felem4 {as_nat4 arg2 < prime} -> Tot (r : felem4 {as_nat4 r < prime /\ as_nat4 r == (as_nat4 arg1 - as_nat4 arg2) % prime})

val get_high_part: a: uint64 -> Tot (r: uint32{uint_v r == uint_v a / (pow2 32)})

val get_low_part: a: uint64 -> Tot (r: uint32{uint_v r == uint_v a % (pow2 32)}) 

val store_high_low_u: high: uint32 -> low: uint32 -> Tot (r: uint64 {uint_v r = uint_v high * pow2 32+ uint_v low})

val reduction_prime_2prime: a: felem4 -> Tot (r:felem4{as_nat4 r == as_nat4 a % prime})

val shift_left_felem: input: felem4{as_nat4 input < prime} -> Tot (r: felem4 {as_nat4 r == (as_nat4 input * 2) % prime})

inline_for_extraction noextract
val upload_prime: unit -> Tot (r: felem4 {as_nat4 r = prime})

val shift_256: c: felem4 -> Tot (r: felem8{wide_as_nat4 r = as_nat4 c * pow2 256})
 

val montgomery_multiplication: a: felem4 {as_nat4 a < prime} -> b: felem4{as_nat4 b < prime}  -> 
  Tot (result: felem4 {as_nat4 result = as_nat4 a * as_nat4 b * modp_inv2 (pow2 256) % prime})

val cube_tuple: a: felem4{as_nat4 a < prime} -> Tot (result: felem4{as_nat4 result = (as_nat4 a * as_nat4 a * as_nat4 a * modp_inv2(pow2 256) * modp_inv2 (pow2 256)) % prime})

val quatre_tuple: a: felem4 {as_nat4 a < prime} -> Tot (result : felem4 {as_nat4 result = (as_nat4 a * as_nat4 a * as_nat4 a * as_nat4 a * modp_inv2 (pow2 256) * modp_inv2 (pow2 256) * modp_inv2(pow2 256)) % prime})

val multByThree_tuple: a: felem4{as_nat4 a < prime}  -> Tot (result: felem4{as_nat4 result = (as_nat4 a * 3) % prime})

val multByFour_tuple: a: felem4{as_nat4 a < prime} -> Tot (result : felem4 {as_nat4 result = (as_nat4 a * 4) % prime})

val multByEight_tuple: a: felem4 {as_nat4 a < prime} -> Tot (result: felem4 {as_nat4 result = (as_nat4 a * 8) % prime})

val multByMinusThree_tuple: a: felem4 {as_nat4 a < prime} -> Tot (result: felem4 {as_nat4 result = (as_nat4 a * (-3)) % prime})

val isOne_tuple: a: felem4 -> Tot (r: bool {if as_nat4 a = 1 then r == true else r == false})

val equalFelem: a: felem4 -> b: felem4 -> Tot (r: uint64 {if as_nat4 a = as_nat4 b then uint_v r == pow2 64 - 1 else uint_v r = 0})

val uploadOne: unit -> Tot (r: felem4 {as_nat4 r = 1})

val uploadZero: unit -> Tot (r: felem4 {as_nat4 r = 0})

val isZero_tuple_u: a: felem4 -> Tot (r: uint64 {if as_nat4 a = 0 then uint_v r == pow2 64 - 1 else uint_v r = 0})

val isZero_tuple_b: a: felem4 ->  Tot (r: bool {if as_nat4 a = 0 then r == true else r == false})

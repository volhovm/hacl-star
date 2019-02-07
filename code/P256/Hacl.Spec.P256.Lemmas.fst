module Hacl.Spec.P256.Lemmas

open Lib.IntTypes
open FStar.Math.Lemmas
open FStar.Math.Lib
module D = Hacl.Spec.Curve25519.Field64.Definition
module C =  Hacl.Spec.Curve25519.Field64.Core

open FStar.Mul

open Hacl.Spec.P256.Definitions

assume val log_and: a: uint64 -> b: uint64{uint_v b == 0 \/ uint_v b == pow2 64 - 1} -> 
Lemma (if uint_v b = 0 then uint_v (logand a b) == 0 else uint_v (logand a b) == uint_v a)

assume val log_or: a: uint64 -> b: uint64 {uint_v b == 0 \/ uint_v a == 0} -> 
Lemma (if uint_v b = 0 then uint_v (logor a b) == uint_v a else uint_v (logor a b) == uint_v b)

assume val log_not_lemma: b: uint64{uint_v b == 0 \/ uint_v b == pow2 64 - 1} -> 
Lemma(if uint_v b = 0 then uint_v (lognot (b)) == pow2 64 -1 else uint_v (lognot b) == 0)


val lemma_nat_4: f: felem4 -> Lemma (D.as_nat4 f < pow2 256)

let lemma_nat_4 f = 
  let (s0, s1, s2, s3) = f in 
  let r_n = D.as_nat4 f in 
  let r = uint_v s0 + uint_v s1 * pow2 64 + uint_v s2 * pow2 64 * pow2 64 + 
  uint_v s3 * pow2 64 * pow2 64 * pow2 64 in 
  assert(r_n == r);
  assert_norm(r < pow2 256)


val prime_lemma: a: nat -> Lemma (if a >= prime && a < (prime * 2) then
a % prime == a - prime else True)

let prime_lemma a = 
  assert_norm (prime > 0);
  if a >= prime && a < prime * 2 then 
  modulo_lemma (a - prime) prime;
  lemma_mod_plus (a - prime) 1 prime

val lemma_for_multiplication_1: 
  a: felem4 {D.as_nat4 a < prime} -> 
  b: felem4 {D.as_nat4 b < prime} -> 
  Lemma (ensures (
let p256 = (u64 0xffffffffffffffff, u64 0xffffffff, u64 0, u64 0xffffffff00000001) in 
let (x8, c) = C.add4 a b in 
let (x16, r) = C.sub4 c p256 in 
uint_v x8 == 1 ==> uint_v x16 == 1))

let lemma_for_multiplication_1 a b = 
  let p256 = (u64 0xffffffffffffffff, u64 0xffffffff, u64 0, u64 0xffffffff00000001) in 
  assert_norm(prime < pow2 256);
  assert_norm(D.as_nat4 p256 == prime);
  let (x8, c) = C.add4 a b in 
  let (x16, r) = C.sub4 c p256 in   
  lemma_nat_4 c

val small_modulo_lemma_extended: a: nat -> b: pos -> Lemma (if a < b then a % b = a else True)

let small_modulo_lemma_extended a b = 
  if a < b then 
    small_modulo_lemma_1 a b



val lemma_add4_zero: a: felem4 -> b: felem4 -> Lemma (let (c, r) = C.add4 a b in 
  if D.as_nat4 a = 0 then uint_v c == 0 /\ D.as_nat4 r == D.as_nat4 b 
  else if D.as_nat4 b = 0 then uint_v c == 0 /\ D.as_nat4 r == D.as_nat4 a 
  else True)

let lemma_add4_zero a b = ()
  
val lemma_adding_prime: a: felem4{D.as_nat4 a < prime}  -> b: felem4{D.as_nat4 b < prime} -> Lemma (let (c, r) = C.sub4 a b in 
  if D.as_nat4 a < D.as_nat4 b then 
    (D.as_nat4 a - D.as_nat4 b) % prime == (D.as_nat4 r - pow2 256 + prime) 
  else
     (D.as_nat4 a - D.as_nat4 b) % prime == D.as_nat4 r)

let lemma_adding_prime a b = 
  let (c, r) = C.sub4 a b in 
  if D.as_nat4 a < D.as_nat4 b then 
    begin 
      let result = D.as_nat4 r - pow2 256 in 
      small_modulo_lemma_extended (result + prime) prime;
      modulo_addition_lemma result prime 1
      end
  else
    begin
      small_modulo_lemma_extended (D.as_nat4 r) prime
    end

val lemma_enough_to_carry: a: felem4 -> b: felem4 -> Lemma (
  if D.as_nat4 b >= (pow2 256 - D.as_nat4 a) then 
    let (c, r) = C.add4 a b in 
    uint_v c == 1
    else True)
    

let lemma_enough_to_carry a b = 
 if D.as_nat4 b >= (pow2 256 - D.as_nat4 a) then begin
  let (c, r) = C.add4 a b in 
    lemma_nat_4 r
  end
  else
  ()


val lemma_sub_add: a: felem4 -> b:felem4 ->
  prime_temp: felem4{if D.as_nat4 a < D.as_nat4 b then D.as_nat4 prime_temp == prime else D.as_nat4 prime_temp == 0} ->  
  r: felem4{if D.as_nat4 a < D.as_nat4 b then (D.as_nat4 a - D.as_nat4 b) % prime ==
    (D.as_nat4 r - pow2 256 + prime) else (D.as_nat4 a - D.as_nat4 b) % prime == D.as_nat4 r} -> 
 Lemma(let (c, r1) = C.add4 prime_temp r in (D.as_nat4 a - D.as_nat4 b) % prime == D.as_nat4 r1)

let lemma_sub_add a b prime_temp r = 
  if D.as_nat4 a >= D.as_nat4 b then ()
  else
    begin
      let result = D.as_nat4 r - pow2 256 + prime in 
      let (c, r1) = C.add4 prime_temp r in 
      lemma_enough_to_carry prime_temp r
    end


val equal_plus_minus : a: felem4 -> b: nat -> Lemma (D.as_nat4 a + b - b == D.as_nat4 a)

let equal_plus_minus a b = ()
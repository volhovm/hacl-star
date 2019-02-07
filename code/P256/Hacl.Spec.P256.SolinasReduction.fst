module Hacl.Spec.P256.SolinasReduction

open Lib.IntTypes 
open FStar.Math.Lemmas
open FStar.Math.Lib
module D = Hacl.Spec.Curve25519.Field64.Definition
module C =  Hacl.Spec.Curve25519.Field64.Core
open FStar.Mul
open Lib.Sequence

open Hacl.Spec.P256.Core
open Hacl.Spec.P256.Definitions

let prime = pow2 256 - pow2 224 + pow2 192 + pow2 96 -1 

#reset-options " --z3rlimit 300"


val p256_prime_value: n : nat ->  Lemma
	(requires (n = 256))
	(ensures (pow2 n - pow2 224 + pow2 192 + pow2 96 -1 = 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff))
	[SMTPat (pow2 n - pow2 224 + pow2 192 + pow2 96 - 1)]

let p256_prime_value n = 
	assert_norm(pow2 256 - pow2 224 + pow2 192 + pow2 96 - 1 = 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff)


val c8_computations: c8: nat{c8 < pow2 32}  -> 
  Lemma(ensures ((c8 * pow2 256) % prime == c8 * (pow2 (7 * 32) - pow2 (6 * 32) - pow2 (3 * 32) + 1) % prime))

let c8_computations c8 = 
  assert_norm(pow2 256 % prime = pow2 224 - pow2 192 - pow2 96 + 1);
  lemma_mod_mul_distr_r c8 (pow2 256) prime;
  lemma_mod_mul_distr_r c8 (pow2 224 - pow2 192 - pow2 96 + 1) prime;
  ()


val inside_mod: a: int-> c: pos ->  c1: int -> c2: int {c1 % c == c2 % c} -> Lemma ((a + c1) % c == (a + c2) % c)

let inside_mod a c c1 c2 = 
  modulo_distributivity a c1 c;
  modulo_distributivity a c2 c;
  assert((a + c1) % c == (a % c + c1 % c) % c);
  assert((a + c1) % c == (a % c + c2 % c) % c);
  assert((a + c1) % c == (a + c2) % c)

val c8_add: c8: nat{c8 < pow2 32} ->a: int ->  Lemma (ensures (a + c8 + c8*pow2 (7*32) - c8 * pow2 (3 * 32) - c8 * pow2 (6 * 32)) % prime == (a + c8 * pow2 256) % prime)

let c8_add c8 a = 
  c8_computations c8;
  let bracket1 = c8 * pow2 256 in 
  let bracket2 = c8 + c8*pow2 (7*32) - c8 * pow2 (3 * 32) - c8 * pow2 (6 * 32) in 
  inside_mod a prime bracket2 bracket1


val c9_computations: c9: nat {c9 < pow2 32} -> 
  Lemma (ensures (c9 * pow2 288 % prime == c9 * (- pow2 (6 * 32) - pow2 (4 * 32) - pow2 (3 * 32) + pow2 (1 * 32) + 1) % prime))

let c9_computations c9 = 
  lemma_mod_mul_distr_r c9 (pow2 288) prime;
  assert_norm (pow2 288 % prime == (pow2 32 - pow2 192 - pow2 128 - pow2 96 + 1) % prime);
  lemma_mod_mul_distr_r c9 (pow2 32 - pow2 192 - pow2 128 - pow2 96 + 1) prime


val c9_add: c9: nat{c9 < pow2 32} -> a: int -> Lemma (ensures (a + c9*pow2 32 + c9 - c9 * pow2 (6*32) - c9 * pow2 (4 * 32) - c9* pow2 (3 * 32)) % prime == (a + c9 * pow2 288) % prime)

let c9_add c9 a = 
  c9_computations c9;
  let bracket1 = c9 * pow2 (32 * 9) in 
  let bracket2 = c9*pow2 32 + c9 - c9 * pow2 (6*32) - c9 * pow2 (4 * 32) - c9* pow2 (3 * 32) in 
  inside_mod a prime bracket2 bracket1


val c10_computations: c10: nat {c10 < pow2 32} -> Lemma (ensures (c10 * pow2 (10* 32) % prime == (c10 * (-pow2 (7 * 32) - pow2 (5*32) - pow2 (4*32) + pow2 32 + pow2 (2 * 32))) % prime))

let c10_computations c10 = 
  lemma_mod_mul_distr_r c10 (pow2 (32 * 10)) prime;
  assert_norm (pow2 (10 * 32) % prime = (-pow2 224 - pow2 160 - pow2 128 + pow2 32 + pow2 64)% prime);
  lemma_mod_mul_distr_r c10 (-pow2 224 - pow2 160 - pow2 128 + pow2 32 + pow2 64) prime


val c10_add: c10: nat {c10 < pow2 32} -> a: int -> Lemma (ensures ((a - c10 * pow2 (7* 32) - c10 * pow2 (5 * 32) - c10 * pow2 (4 * 32) + c10 * pow2 32 + c10 * pow2 (2 * 32)) % prime == (a + c10* pow2 (10 * 32)) % prime))

let c10_add c10 a = 
  c10_computations c10;
  let bracket2 = - c10 * pow2 (7* 32) - c10 * pow2 (5 * 32) - c10 * pow2 (4 * 32) + c10 * pow2 32 + c10 * pow2 (2 * 32) in 
  let bracket1 = c10 * pow2 (10 * 32) in 
  inside_mod a prime bracket2 bracket1


val c11_computations: c11: nat { c11 < pow2 32}  -> Lemma (ensures (c11 * pow2 (11 * 32) % prime == (c11 * (2 * pow2 96 + pow2 64 - 1 - pow2 224 - pow2 160)) % prime))

let c11_computations c11  = 
  assert_norm((pow2 (11 * 32) % prime == (2 * pow2 96 + pow2 64 - 1 - pow2 224 - pow2 160) % prime));
  lemma_mod_mul_distr_r c11 (pow2 (11 * 32)) prime;
  lemma_mod_mul_distr_r c11 (2 * pow2 96 + pow2 64 - 1 - pow2 224 - pow2 160) prime


val c11_add: c11: nat {c11 < pow2 32} -> a: int -> Lemma ((a +  c11 * 2 * pow2 96 +  c11 * pow2 64 - c11 - c11* pow2 224 - c11 * pow2 160) % prime == (a + c11 * pow2 (11 * 32)) % prime)

let c11_add c11 a = 
  c11_computations c11;
  let bracket1 = c11 * pow2 (11 * 32) in 
  let bracket2 = c11 * 2 * pow2 96 +  c11 * pow2 64 - c11 - c11* pow2 224 - c11 * pow2 160 in 
  inside_mod a prime bracket2 bracket1


val c12_computations: c12: nat {c12 < pow2 32} -> Lemma (ensures (c12 * pow2 (12 * 32) % prime == (c12 * 2 * pow2 (4 * 32) + c12 * 2 * pow2 (3 * 32) - c12 * pow2 32 - c12 - c12 * pow2 (7 * 32))% prime))

let c12_computations c12 = 
  assert_norm (pow2 (12 * 32) % prime == (2 * pow2 (4 * 32) + 2 * pow2 (3 * 32) - pow2 32 - 1 - pow2 (7 * 32))% prime);
  lemma_mod_mul_distr_r c12 (pow2 (12 * 32)) prime;
  lemma_mod_mul_distr_r c12 (2 * pow2 (4 * 32) + 2 * pow2 (3 * 32) - pow2 32 - 1 - pow2 (7 * 32)) prime


val c12_add: c12: nat {c12 < pow2 32} -> a: int -> Lemma ((a +c12 * 2 * pow2 (4 * 32) + c12* 2 * pow2 (3 * 32) - c12* pow2 32 - c12 - c12 * pow2 (7 * 32)) % prime == (a + c12 * pow2 (12 * 32)) % prime)

let c12_add c12 a = 
  c12_computations c12;
  let bracket1 = c12 * pow2 (12 * 32) in 
  let bracket2 = c12 * 2 * pow2 (4 * 32) + c12* 2 * pow2 (3 * 32) - c12* pow2 32 - c12-  c12* pow2 (7 * 32) in 
  inside_mod a prime bracket2 bracket1


val c13_computations: c13: nat {c13 < pow2 32} -> Lemma ((c13 * pow2 (13 * 32) % prime == (2 * c13 * pow2 (5 * 32) + 2 * c13 * pow2 (4 * 32) + c13 * pow2 (3 * 32) + c13 * pow2 (6 * 32) - c13 * pow2 (2 * 32) - c13 * pow2 32 - c13 - c13 * pow2 (7 * 32)) % prime))

let c13_computations c13 = 
  assert_norm (pow2 (13 * 32) % prime == (2 *  pow2 (5 * 32) + 2 * pow2 (4 * 32) +  pow2 (3 * 32) + pow2 (6 * 32) - pow2 (2 * 32) - pow2 32 - 1 -  pow2 (7 * 32)) % prime);
  lemma_mod_mul_distr_r c13 (pow2 (13 * 32)) prime;
  lemma_mod_mul_distr_r c13 (2 *  pow2 (5 * 32) + 2 * pow2 (4 * 32) +  pow2 (3 * 32) + pow2 (6 * 32) - pow2 (2 * 32) - pow2 32 - 1 -  pow2 (7 * 32)) prime


val c13_add : c13: nat {c13 < pow2 32} -> a: int -> Lemma ((a+ 2 * c13 * pow2 (5 * 32) + 2 * c13 * pow2 (4 * 32) + c13 * pow2 (3 * 32) + c13 * pow2 (6 * 32) - c13 * pow2 (2 * 32) - c13 * pow2 32 - c13 - c13 * pow2 (7 * 32)) % prime == (a + c13 * pow2 (13 * 32)) % prime)

let c13_add c13 a = 
  c13_computations c13;
  let bracket1 = c13 * pow2 (13 * 32) in 
  let bracket2 = 2 * c13 * pow2 (5 * 32) + 2 * c13 * pow2 (4 * 32) + c13 * pow2 (3 * 32) + c13 * pow2 (6 * 32) - c13 * pow2 (2 * 32) - c13 * pow2 32 - c13 - c13 * pow2 (7 * 32) in 
  inside_mod a prime bracket2 bracket1


val c14_computations: c14: nat {c14 < pow2 32} -> Lemma ((c14 * pow2 (14 * 32) % prime == (2 * c14 * pow2 (6 * 32) + 2 * c14 * pow2 (5 * 32) +  c14 * pow2 (6 * 32) + c14* pow2 (4 * 32) - c14 * pow2 (2 * 32) - c14 * pow2 32 - c14) % prime))

let c14_computations c14 = 
  assert_norm (pow2 (14 * 32) % prime == (2 * pow2 (6 * 32) + 2 * pow2 (5 * 32) +  pow2 (6 * 32) + pow2 (4 * 32) - pow2 (2 * 32) - pow2 32 - 1) % prime);
  lemma_mod_mul_distr_r c14 (pow2 (14 * 32)) prime;
  lemma_mod_mul_distr_r c14 (2 * pow2 (6 * 32) + 2 * pow2 (5 * 32) +  pow2 (6 * 32) + pow2 (4 * 32) - pow2 (2 * 32) - pow2 32 - 1) prime


val c14_add: c14: nat {c14 < pow2 32} -> a: int -> Lemma ((a + 2 * c14 * pow2 (6 * 32) + 2 * c14 * pow2 (5 * 32) +  c14 * pow2 (6 * 32) + c14* pow2 (4 * 32) - c14 * pow2 (2 * 32) - c14 * pow2 32 - c14) % prime == (a + c14 * pow2 (14 * 32)) % prime)

let c14_add c14 a = 
  c14_computations c14;
  let bracket1 = c14 * pow2 (14 * 32) in 
  let bracket2 = 2 * c14 * pow2 (6 * 32) + 2 * c14 * pow2 (5 * 32) +  c14 * pow2 (6 * 32) + c14* pow2 (4 * 32) - c14 * pow2 (2 * 32) - c14 * pow2 32 - c14 in 
  inside_mod a prime bracket2 bracket1


val c15_computations: c15: nat { c15 < pow2 32} -> Lemma ((c15 * pow2 (15 * 32) % prime == (2 * c15 * pow2 (7 * 32) + 2 * c15 * pow2 (6 * 32) + c15 * pow2 (7 * 32) + c15 * pow2 (5 * 32) - c15 * pow2 (3 * 32) - c15 * pow2 (2 * 32) - c15 * pow2 32)% prime)) 

let c15_computations c15 = 
  assert_norm (pow2 (15 * 32) % prime ==  (2 * pow2 (7 * 32) + 2 * pow2 (6 * 32) +pow2 (7 * 32) + pow2 (5 * 32) -  pow2 (3 * 32) - pow2 (2 * 32) - pow2 32) % prime);
  lemma_mod_mul_distr_r c15 (pow2 (15 * 32)) prime;
  lemma_mod_mul_distr_r c15  (2 * pow2 (7 * 32) + 2 * pow2 (6 * 32) +pow2 (7 * 32) + pow2 (5 * 32) -  pow2 (3 * 32) - pow2 (2 * 32) - pow2 32) prime
  

val c15_add : c15: nat {c15 < pow2 32} -> a: int -> Lemma ((a + c15 * pow2 (15 * 32)) % prime == (a + 2 * c15 * pow2 (7 * 32) + 2 * c15 * pow2 (6 * 32) + c15 * pow2 (7 * 32) + c15 * pow2 (5 * 32) - c15 * pow2 (3 * 32) - c15 * pow2 (2 * 32) - c15 * pow2 32)% prime)

let c15_add c15 a = 
  c15_computations c15;
  let bracket1 = c15 * pow2 (15 * 32) in 
  let bracket2 = 2 * c15 * pow2 (7 * 32) + 2 * c15 * pow2 (6 * 32) + c15 * pow2 (7 * 32) + c15 * pow2 (5 * 32) - c15 * pow2 (3 * 32) - c15 * pow2 (2 * 32) - c15 * pow2 32 in 
  inside_mod a prime bracket2 bracket1

#reset-options " --z3rlimit 500 --max_fuel 1 "

val solaris_reduction: c0_n: nat -> c1_n : nat -> c2_n: nat -> c3_n: nat -> c4_n: nat -> c5_n: nat -> c6_n: nat -> c7_n: nat -> c8_n: nat{c8_n < pow2 32} -> c9_n: nat{c9_n < pow2 32} -> c10_n: nat{c10_n < pow2 32} -> c11_n: nat{c11_n < pow2 32} -> c12_n: nat{c12_n < pow2 32} -> c13_n: nat{c13_n < pow2 32} -> c14_n: nat{c14_n < pow2 32}  -> c15_n: nat{c15_n < pow2 32} ->
n: int {n = c0_n + c1_n * pow2 32 + c2_n * pow2 (2 * 32) + c3_n * pow2 (3 * 32) + c4_n * pow2 (4 * 32) + c5_n * pow2 (5 * 32) + c6_n * pow2 (6 * 32) + c7_n * pow2 (7 * 32) +
2 * c11_n * pow2 (3 * 32) + 2 * c12_n * pow2 (4 * 32) + 2* c13_n * pow2 (5* 32)  + 2* c14_n * pow2 (6 * 32) + 2 * c15_n * pow2 (7 * 32) + 
2 * c12_n * pow2 (3 * 32) + 2 * c13_n * pow2 (4 * 32) + 2 * c14_n * pow2 (5* 32) + 2* c15_n * pow2 (6 * 32) +
c8_n + c9_n * pow2 32 + c10_n * pow2 (2 * 32) + c14_n * pow2 (6 * 32) +  c15_n * pow2 (7 * 32) + 
c9_n + c10_n * pow2 32 + c11_n * pow2 (2 * 32) + c13_n * pow2 (3 * 32) + c14_n * pow2 (4 * 32) + c15_n * pow2 (5 * 32) + c13_n * pow2 (6 * 32) + c8_n * pow2 (7 * 32)  
- c11_n - c12_n * pow2 32 - c13_n * pow2 (2 * 32) - c8_n * pow2 (6 * 32) - c10_n * pow2 (7 * 32)
- c12_n - c13_n * pow2 32 - c14_n * pow2 (2 * 32) - c15_n * pow2 (3 * 32) - c9_n * pow2 (6 * 32) - c11_n * pow2 (7 * 32)
- c13_n - c14_n * pow2 32 - c15_n * pow2 (2 * 32) - c8_n * pow2 (3* 32) - c9_n * pow2 (4 * 32) - c10_n * pow2 (5 * 32) - c12_n * pow2 (7 * 32)
- c14_n - c15_n * pow2 32 - c9_n * pow2 (3 * 32) - c10_n * pow2 (4* 32) - c11_n * pow2 (5 * 32) - c13_n * pow2 (7 * 32)} -> 
Lemma (n % prime == (c0_n + c1_n * pow2 32 + c2_n * pow2 (2 * 32) + c3_n * pow2 (3 * 32) + c4_n * pow2 (4 * 32) + c5_n * pow2 (5 * 32) + c6_n * pow2 (6 * 32) + c7_n * pow2 (7 * 32) + c8_n * pow2 256 + c9_n * pow2 288 + c10_n * pow2 (10 * 32)  + c11_n * pow2 (11 * 32) + c12_n * pow2 (12 * 32) + c13_n* pow2 (13 * 32) + c14_n * pow2 (14 * 32) + c15_n * pow2 (15 * 32)) % prime)



let solaris_reduction c0_n c1_n c2_n c3_n c4_n c5_n c6_n c7_n c8_n c9_n c10_n c11_n c12_n c13_n c14_n c15_n n=
    assert(n = c0_n + c1_n * pow2 32 + c2_n * pow2 (2 * 32) + c3_n * pow2 (3 * 32) + c4_n * pow2 (4 * 32) + c5_n * pow2 (5 * 32) + c6_n * pow2 (6 * 32) + c7_n * pow2 (7 * 32) +
2 * c11_n * pow2 (3 * 32) + 2 * c12_n * pow2 (4 * 32) + 2* c13_n * pow2 (5* 32)  + 2* c14_n * pow2 (6 * 32) + 2 * c15_n * pow2 (7 * 32) + 
2 * c12_n * pow2 (3 * 32) + 2 * c13_n * pow2 (4 * 32) + 2 * c14_n * pow2 (5* 32) + 2* c15_n * pow2 (6 * 32) +
c8_n + c9_n * pow2 32 + c10_n * pow2 (2 * 32) + c14_n * pow2 (6 * 32) +  c15_n * pow2 (7 * 32) + 
c9_n + c10_n * pow2 32 + c11_n * pow2 (2 * 32) + c13_n * pow2 (3 * 32) + c14_n * pow2 (4 * 32) + c15_n * pow2 (5 * 32) + c13_n * pow2 (6 * 32) + c8_n * pow2 (7 * 32)  
- c11_n - c12_n * pow2 32 - c13_n * pow2 (2 * 32) - c8_n * pow2 (6 * 32) - c10_n * pow2 (7 * 32)
- c12_n - c13_n * pow2 32 - c14_n * pow2 (2 * 32) - c15_n * pow2 (3 * 32) - c9_n * pow2 (6 * 32) - c11_n * pow2 (7 * 32)
- c13_n - c14_n * pow2 32 - c15_n * pow2 (2 * 32) - c8_n * pow2 (3* 32) - c9_n * pow2 (4 * 32) - c10_n * pow2 (5 * 32) - c12_n * pow2 (7 * 32)
- c14_n - c15_n * pow2 32 - c9_n * pow2 (3 * 32) - c10_n * pow2 (4* 32) - c11_n * pow2 (5 * 32) - c13_n * pow2 (7 * 32));
  
  c8_computations c8_n;
  
  let w_c8 : int = c0_n + c1_n * pow2 32 + c2_n * pow2 (2 * 32) + c3_n * pow2 (3 * 32) + c4_n * pow2 (4 * 32) + c5_n * pow2 (5 * 32) + c6_n * pow2 (6 * 32) + c7_n * pow2 (7 * 32) +
2 * c11_n * pow2 (3 * 32) + 2 * c12_n * pow2 (4 * 32) + 2* c13_n * pow2 (5* 32)  + 2* c14_n * pow2 (6 * 32) + 2 * c15_n * pow2 (7 * 32) + 
2 * c12_n * pow2 (3 * 32) + 2 * c13_n * pow2 (4 * 32) + 2 * c14_n * pow2 (5* 32) + 2* c15_n * pow2 (6 * 32) + c9_n * pow2 32 + c10_n * pow2 (2 * 32) + c14_n * pow2 (6 * 32) +  c15_n * pow2 (7 * 32) + 
c9_n + c10_n * pow2 32 + c11_n * pow2 (2 * 32) + c13_n * pow2 (3 * 32) + c14_n * pow2 (4 * 32) + c15_n * pow2 (5 * 32) + c13_n * pow2 (6 * 32)  
- c11_n - c12_n * pow2 32 - c13_n * pow2 (2 * 32)  - c10_n * pow2 (7 * 32)
- c12_n - c13_n * pow2 32 - c14_n * pow2 (2 * 32) - c15_n * pow2 (3 * 32) - c9_n * pow2 (6 * 32) - c11_n * pow2 (7 * 32)
- c13_n - c14_n * pow2 32 - c15_n * pow2 (2 * 32) - c9_n * pow2 (4 * 32) - c10_n * pow2 (5 * 32) - c12_n * pow2 (7 * 32)
- c14_n - c15_n * pow2 32 - c9_n * pow2 (3 * 32) - c10_n * pow2 (4* 32) - c11_n * pow2 (5 * 32) - c13_n * pow2 (7 * 32) in 

  assert(w_c8 + c8_n + c8_n * pow2 (7 * 32) - c8_n * pow2 (6 * 32) - c8_n * pow2 (3 * 32) == n);
  assert((w_c8 + c8_n + c8_n * pow2 (7 * 32) - c8_n * pow2 (6 * 32) - c8_n * pow2 (3 * 32)) % prime == n % prime);
  c8_add c8_n w_c8;
  assert((w_c8 + c8_n + c8_n * pow2 (7 * 32) - c8_n * pow2 (6 * 32) - c8_n * pow2 (3 * 32)) % prime == (w_c8 + c8_n * pow2 256) % prime);

  let w = w_c8 + c8_n * pow2 256 in   
  assert(w % prime == n % prime);

  let w_c8_c9 : int = c0_n + c1_n * pow2 32 + c2_n * pow2 (2 * 32) + c3_n * pow2 (3 * 32) + c4_n * pow2 (4 * 32) + c5_n * pow2 (5 * 32) + c6_n * pow2 (6 * 32) + c7_n * pow2 (7 * 32) + c8_n * pow2 256 + 
  2 * c11_n * pow2 (3 * 32) + 2 * c12_n * pow2 (4 * 32) + 2* c13_n * pow2 (5* 32)  + 2* c14_n * pow2 (6 * 32) + 2 * c15_n * pow2 (7 * 32) +
  2 * c12_n * pow2 (3 * 32) + 2 * c13_n * pow2 (4 * 32) + 2 * c14_n * pow2 (5* 32) + 2* c15_n * pow2 (6 * 32) + c10_n * pow2 (2 * 32) + c14_n * pow2 (6 * 32) +  c15_n * pow2 (7 * 32) + 
c10_n * pow2 32 + c11_n * pow2 (2 * 32) + c13_n * pow2 (3 * 32) + c14_n * pow2 (4 * 32) + c15_n * pow2 (5 * 32) + c13_n * pow2 (6 * 32)  
- c11_n - c12_n * pow2 32 - c13_n * pow2 (2 * 32)  - c10_n * pow2 (7 * 32)
- c12_n - c13_n * pow2 32 - c14_n * pow2 (2 * 32) - c15_n * pow2 (3 * 32) - c11_n * pow2 (7 * 32)
- c13_n - c14_n * pow2 32 - c15_n * pow2 (2 * 32) - c10_n * pow2 (5 * 32) - c12_n * pow2 (7 * 32)
- c14_n - c15_n * pow2 32 - c10_n * pow2 (4* 32) - c11_n * pow2 (5 * 32) - c13_n * pow2 (7 * 32) in 

 assert(w_c8_c9 + c9_n* pow2 32 + c9_n - c9_n* pow2 (6 * 32) - c9_n * pow2 (4 * 32) - c9_n * pow2(3 * 32)  == w);
 c9_add c9_n w_c8_c9;
 assert((w_c8_c9 + c9_n* pow2 32 + c9_n - c9_n* pow2 (6 * 32) - c9_n * pow2 (4 * 32) - c9_n * pow2(3 * 32)) % prime == (w_c8_c9 + c9_n * pow2 288) % prime);

 let w = w_c8_c9 + c9_n * pow2 288 in 
 assert(w % prime == n % prime);
 
 let w_c8_c9_c10: int =  c0_n + c1_n * pow2 32 + c2_n * pow2 (2 * 32) + c3_n * pow2 (3 * 32) + c4_n * pow2 (4 * 32) + c5_n * pow2 (5 * 32) + c6_n * pow2 (6 * 32) + c7_n * pow2 (7 * 32) + c8_n * pow2 256 + c9_n * pow2 288 +
  2 * c11_n * pow2 (3 * 32) + 2 * c12_n * pow2 (4 * 32) + 2* c13_n * pow2 (5* 32)  + 2* c14_n * pow2 (6 * 32) + 2 * c15_n * pow2 (7 * 32) +
  2 * c12_n * pow2 (3 * 32) + 2 * c13_n * pow2 (4 * 32) + 2 * c14_n * pow2 (5* 32) + 2* c15_n * pow2 (6 * 32) + c14_n * pow2 (6 * 32) +  c15_n * pow2 (7 * 32) + 
c11_n * pow2 (2 * 32) + c13_n * pow2 (3 * 32) + c14_n * pow2 (4 * 32) + c15_n * pow2 (5 * 32) + c13_n * pow2 (6 * 32)  
- c11_n - c12_n * pow2 32 - c13_n * pow2 (2 * 32)
- c12_n - c13_n * pow2 32 - c14_n * pow2 (2 * 32) - c15_n * pow2 (3 * 32) - c11_n * pow2 (7 * 32)
- c13_n - c14_n * pow2 32 - c15_n * pow2 (2 * 32) - c12_n * pow2 (7 * 32)
- c14_n - c15_n * pow2 32 - c11_n * pow2 (5 * 32) - c13_n * pow2 (7 * 32)  in 

  assert(w_c8_c9_c10 + c10_n* pow2 (2 * 32) - c10_n * pow2 (7 * 32) - c10_n * pow2 (5 * 32) - c10_n * pow2 (4 * 32) + c10_n * pow2 32 == w);
  c10_add c10_n w_c8_c9_c10;
  let w = w_c8_c9_c10 + c10_n * pow2 (10 * 32) in
  let w_c8_c9_c10_c11: int = 
c0_n + c1_n * pow2 32 + c2_n * pow2 (2 * 32) + c3_n * pow2 (3 * 32) + c4_n * pow2 (4 * 32) + c5_n * pow2 (5 * 32) + c6_n * pow2 (6 * 32) + c7_n * pow2 (7 * 32) + c8_n * pow2 256 + c9_n * pow2 288 + c10_n * pow2 (10 * 32)  + 
2 * c12_n * pow2 (4 * 32) + 2 * c13_n * pow2 (5 * 32)  + 2* c14_n * pow2 (6 * 32) + 2 * c15_n * pow2 (7 * 32) +
2 * c12_n * pow2 (3 * 32) + 2 * c13_n * pow2 (4 * 32) + 2 * c14_n * pow2 (5 * 32) + 2 * c15_n * pow2 (6 * 32) + 
c14_n * pow2 (6 * 32) + c15_n * pow2 (7 * 32) + 
c13_n * pow2 (3 * 32) + c14_n * pow2 (4 * 32) + c15_n * pow2 (5 * 32) + c13_n * pow2 (6 * 32)  
- c12_n * pow2 32 - c13_n * pow2 (2 * 32)
- c12_n - c13_n * pow2 32 - c14_n * pow2 (2 * 32) - c15_n * pow2 (3 * 32) 
- c13_n - c14_n * pow2 32 - c15_n * pow2 (2 * 32) - c12_n * pow2 (7 * 32)
- c14_n - c15_n * pow2 32 - c13_n * pow2 (7 * 32) 
in 

assert(w_c8_c9_c10_c11  + 2 * c11_n * pow2 (3 * 32) + c11_n * pow2 (2 * 32) - c11_n - c11_n * pow2 (7*32) - c11_n * pow2 (5 * 32) == w);

c11_add c11_n w_c8_c9_c10_c11;
let w = w_c8_c9_c10_c11 + c11_n * pow2 (11 * 32) in 

assert(w % prime == n % prime);

  let w_c8_c9_c10_c11_c12: int = 
  c0_n + c1_n * pow2 32 + c2_n * pow2 (2 * 32) + c3_n * pow2 (3 * 32) + c4_n * pow2 (4 * 32) + c5_n * pow2 (5 * 32) + c6_n * pow2 (6 * 32) + c7_n * pow2 (7 * 32) + c8_n * pow2 256 + c9_n * pow2 288 + c10_n * pow2 (10 * 32)  + c11_n * pow2 (11 * 32) +
  
2 * c13_n * pow2 (5 * 32)  + 2* c14_n * pow2 (6 * 32) + 2 * c15_n * pow2 (7 * 32) +
2 * c13_n * pow2 (4 * 32) + 2 * c14_n * pow2 (5 * 32) + 2 * c15_n * pow2 (6 * 32) + 
c14_n * pow2 (6 * 32) + c15_n * pow2 (7 * 32) + 
c13_n * pow2 (3 * 32) + c14_n * pow2 (4 * 32) + c15_n * pow2 (5 * 32) + c13_n * pow2 (6 * 32)  
- c13_n * pow2 (2 * 32)
- c13_n * pow2 32 - c14_n * pow2 (2 * 32) - c15_n * pow2 (3 * 32) 
- c13_n - c14_n * pow2 32 - c15_n * pow2 (2 * 32)
- c14_n - c15_n * pow2 32 - c13_n * pow2 (7 * 32) in 
  
  assert(w_c8_c9_c10_c11_c12 + 2 * c12_n * pow2 (4 * 32) + 2 * c12_n * pow2 (3 * 32) - c12_n * pow2 32 - c12_n - c12_n * pow2 (7*32) == w);
   
  c12_add c12_n w_c8_c9_c10_c11_c12;
  let w = w_c8_c9_c10_c11_c12 + c12_n * pow2 (12 * 32) in 
  assert(w % prime == n % prime);

  let w_c8_c9_c10_c11_c12_c13: int = 
  c0_n + c1_n * pow2 32 + c2_n * pow2 (2 * 32) + c3_n * pow2 (3 * 32) + c4_n * pow2 (4 * 32) + c5_n * pow2 (5 * 32) + c6_n * pow2 (6 * 32) + c7_n * pow2 (7 * 32) + c8_n * pow2 256 + c9_n * pow2 288 + c10_n * pow2 (10 * 32)  + c11_n * pow2 (11 * 32) + c12_n * pow2 (12 * 32) + 
  2 * c14_n * pow2 (6 * 32) + 2 * c15_n * pow2 (7 * 32) +
  2 * c14_n * pow2 (5 * 32) + 2 * c15_n * pow2 (6 * 32) + 
  c14_n * pow2 (6 * 32) + c15_n * pow2 (7 * 32) + 
  c14_n * pow2 (4 * 32) + c15_n * pow2 (5 * 32) - 
  c14_n * pow2 (2 * 32) - c15_n * pow2 (3 * 32) - 
  c14_n * pow2 32 - c15_n * pow2 (2 * 32) - 
  c14_n - c15_n * pow2 32 in 

  assert(w_c8_c9_c10_c11_c12_c13 + 2 * c13_n * pow2 (5 * 32) + 2 * c13_n * pow2 (4 * 32) + c13_n * pow2 (3 * 32) + c13_n * pow2 (6 * 32) - c13_n * pow2 (2 * 32) - c13_n * pow2 32 - c13_n - c13_n * pow2 (7 * 32) == w);

  c13_add c13_n w_c8_c9_c10_c11_c12_c13;
  let w = w_c8_c9_c10_c11_c12_c13 + c13_n * pow2 (13 * 32) in 
  assert( w % prime == n % prime);

  let w_c8_c9_c10_c11_c12_c13_c14: int = 
   c0_n + c1_n * pow2 32 + c2_n * pow2 (2 * 32) + c3_n * pow2 (3 * 32) + c4_n * pow2 (4 * 32) + c5_n * pow2 (5 * 32) + c6_n * pow2 (6 * 32) + c7_n * pow2 (7 * 32) + c8_n * pow2 256 + c9_n * pow2 288 + c10_n * pow2 (10 * 32)  + c11_n * pow2 (11 * 32) + c12_n * pow2 (12 * 32) + c13_n* pow2 (13 * 32) + 
  2 * c15_n * pow2 (7 * 32) +
  2 * c15_n * pow2 (6 * 32) + 
  c15_n * pow2 (7 * 32) + 
  c15_n * pow2 (5 * 32) - 
  c15_n * pow2 (3 * 32) - 
  c15_n * pow2 (2 * 32) - 
  c15_n * pow2 32 in 

  assert(w_c8_c9_c10_c11_c12_c13_c14 + 2 * c14_n * pow2 (6 * 32) + 2 * c14_n * pow2 (5 * 32) + c14_n * pow2 (6 * 32) + c14_n* pow2 (4 * 32) - c14_n * pow2 (2 * 32) - c14_n * pow2 32 - c14_n == w);

  c14_add c14_n w_c8_c9_c10_c11_c12_c13_c14;
  let w = w_c8_c9_c10_c11_c12_c13_c14 + c14_n * pow2 (14 * 32) in 
  assert(w % prime == n % prime);

  let w_result =  c0_n + c1_n * pow2 32 + c2_n * pow2 (2 * 32) + c3_n * pow2 (3 * 32) + c4_n * pow2 (4 * 32) + c5_n * pow2 (5 * 32) + c6_n * pow2 (6 * 32) + c7_n * pow2 (7 * 32) + c8_n * pow2 256 + c9_n * pow2 288 + c10_n * pow2 (10 * 32)  + c11_n * pow2 (11 * 32) + c12_n * pow2 (12 * 32) + c13_n* pow2 (13 * 32) + c14_n * pow2 (14 * 32) in 
  c15_add c15_n w_result;
  let w = w_result + c15_n * pow2 (15 * 32) in 
  assert(w % prime == n % prime)


val fast_reduction_upload_zero_buffer: input: felem8_32 -> Tot (r: felem4
{
   let (c0, c1, c2, c3, c4, c5, c6, c7) = input in 
   let (r0, r1, r2, r3) = r in 
   D.as_nat4 r == uint_v c0 + uint_v c1 * pow2 (1 * 32) + uint_v c2 * pow2 (2 * 32) + uint_v c3 * pow2 (3 * 32) + uint_v c4 * pow2 (4 * 32) + uint_v c5 * pow2 (5 * 32) + uint_v  c6 * pow2 (6 * 32) + uint_v c7 * pow2 (7 * 32)})

let fast_reduction_upload_zero_buffer input = 
  let (c0, c1, c2, c3, c4, c5, c6, c7) = input in   
  let b0 = store_high_low_u c1 c0 in 
  let b1 = store_high_low_u c3 c2 in 
  let b2 = store_high_low_u c5 c4 in 
  let b3 = store_high_low_u c7 c6 in 
  assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
  assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
  assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
  assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
  assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));
  (b0, b1, b2, b3)

val fast_reduction_upload_first_buffer: input: felem8_32 -> Tot (r: felem4 
{
  let (c8, c9, c10, c11, c12, c13, c14, c15) = input in 
  let (r0, r1, r2, r3) = r in 
  D.as_nat4 r == (uint_v c11 * pow2 (3 * 32) + uint_v c12 * pow2 (4 * 32) + uint_v c13 * pow2 (5 * 32) + uint_v c14 * pow2 (6 * 32) + uint_v c15 * pow2 (7 * 32))})

let fast_reduction_upload_first_buffer input = 
  let (c8, c9, c10, c11, c12, c13, c14, c15) = input in 
  let b0 = u64(0) in 
  let b1 = store_high_low_u c11 (u32 0) in 
  let b2 = store_high_low_u c13 c12 in 
  let b3 = store_high_low_u c15 c14 in 
  assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
  assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
  assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
  assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
  assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));
 (b0, b1, b2, b3)
  

  
val fast_reduction_upload_second_buffer: input: felem8_32 -> Tot (r: felem4
{
  let (c8, c9, c10, c11, c12, c13, c14, c15) = input in 
  let (r0, r1, r2, r3) = r in 
  D.as_nat4 r = uint_v c12 * pow2 (3 * 32) + uint_v c13 * pow2 (4 * 32) + uint_v c14 * pow2 (5* 32) + uint_v c15 * pow2 (6 * 32)})

let fast_reduction_upload_second_buffer input = 
    let (c8, c9, c10, c11, c12, c13, c14, c15) = input in 
    let b0 = u64 (0) in 
    let b1 = store_high_low_u c12 (u32 0) in 
    let b2 = store_high_low_u c14 c13 in 
    let b3 = store_high_low_u (u32 0) c15 in 
      assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
      assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
      assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
      assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
    (b0, b1, b2, b3)


val fast_reduction_upload_third_buffer: input: felem8_32 -> Tot (r: felem4
{
  let (c8, c9, c10, c11, c12, c13, c14, c15) = input in 
  let (r0, r1, r2, r3) = r in 
  D.as_nat4 r = uint_v c8 + uint_v c9 * pow2 32 + uint_v c10 * pow2 (2 * 32) + uint_v c14 * pow2 (6 * 32) + uint_v c15 * pow2 (7 * 32)
  })

let fast_reduction_upload_third_buffer input = 
   let (c8, c9, c10, c11, c12, c13, c14, c15) = input in 
   let b0 = store_high_low_u c9 c8 in 
   let b1 = store_high_low_u (u32 0) c10 in 
   let b2 = u64 0 in 
   let b3 = store_high_low_u c15 c14 in 
     assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
     assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
     assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
     assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
     assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));
   (b0, b1, b2, b3)


val fast_reduction_upload_forth_buffer: input: felem8_32 -> Tot (r: felem4
{
  let (c8, c9, c10, c11, c12, c13, c14, c15) = input in 
  let (r0, r1, r2, r3) = r in 
  D.as_nat4 r = uint_v c9 + uint_v c10 * pow2 32 + uint_v c11 * pow2 (2 * 32) + uint_v c13 * pow2 (3 * 32) + uint_v c14 * pow2 (4 * 32) + uint_v c15 * pow2 (5 * 32) + uint_v c13 * pow2 (6 * 32) + uint_v c8 * pow2 (7 * 32)})

let fast_reduction_upload_forth_buffer input = 
    let (c8, c9, c10, c11, c12, c13, c14, c15) = input in 
    let b0 = store_high_low_u c10 c9 in 
    let b1 = store_high_low_u c13 c11 in 
    let b2 = store_high_low_u c15 c14 in 
    let b3 = store_high_low_u c8 c13 in 
     assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
     assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
     assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
     assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
     assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));
    (b0, b1, b2, b3)


val fast_reduction_upload_fifth_buffer: input: felem8_32 -> Tot (r: felem4 
{
  let (c8, c9, c10, c11, c12, c13, c14, c15) = input in 
  let (r0, r1, r2, r3) = r in 
  D.as_nat4 r = uint_v c11 + uint_v c12 * pow2 32 + uint_v c13 * pow2 (2 * 32) + uint_v c8 * pow2 (6 * 32) + uint_v c10 * pow2 (7 * 32)})

let fast_reduction_upload_fifth_buffer input = 
    let (c8, c9, c10, c11, c12, c13, c14, c15) = input in 
    let b0 = store_high_low_u c12 c11 in 
    let b1 = store_high_low_u (u32 0) c13 in 
    let b2 = u64 0 in 
    let b3 = store_high_low_u c10 c8 in 
     assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
     assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
     assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
     assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
     assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));
    (b0, b1, b2, b3)


val fast_reduction_upload_sixth_buffer: input: felem8_32 -> Tot (r: felem4
{
  let (c8, c9, c10, c11, c12, c13, c14, c15) = input in 
  let (r0, r1, r2, r3) = r in 
  D.as_nat4 r = uint_v c12 + uint_v c13 * pow2 32 + uint_v c14 * pow2 (2 * 32) + uint_v c15 * pow2 (3 * 32) + 
      uint_v c9 * pow2 (6 * 32) + uint_v c11 * pow2 (7 * 32)})

let fast_reduction_upload_sixth_buffer input = 
    let (c8, c9, c10, c11, c12, c13, c14, c15) = input in 
    let b0 = store_high_low_u c13 c12 in 
    let b1 = store_high_low_u c15 c14 in 
    let b2 = u64 0 in 
    let b3 = store_high_low_u c11 c9 in 
     assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
     assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
     assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
     assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
     assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));
   (b0, b1, b2, b3)


val fast_reduction_upload_seventh_buffer: input: felem8_32 -> Tot (r: felem4
{
  let (c8, c9, c10, c11, c12, c13, c14, c15) = input in 
  let (r0, r1, r2, r3) = r in 
  D.as_nat4 r = uint_v c13 + uint_v c14 * pow2 32 + uint_v c15 * pow2 (2 * 32) + uint_v c8 * pow2 (3* 32) +  uint_v c9 * pow2 (4 * 32) + uint_v c10 * pow2 (5 * 32) + uint_v c12 * pow2 (7 * 32)})


let fast_reduction_upload_seventh_buffer input = 
    let (c8, c9, c10, c11, c12, c13, c14, c15) = input in 
    let b0 = store_high_low_u c14 c13 in 
    let b1 = store_high_low_u c8 c15 in 
    let b2 = store_high_low_u c10 c9 in 
    let b3 = store_high_low_u c12 (u32 0) in 
     assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
     assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
     assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
     assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
     assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));
    (b0, b1, b2, b3)

val fast_reduction_upload_eighth_buffer: input: felem8_32 -> Tot (r: felem4
{
  let (c8, c9, c10, c11, c12, c13, c14, c15) = input in 
  let (r0, r1, r2, r3) = r in 
  D.as_nat4 r = uint_v c14 + uint_v c15 * pow2 32 + uint_v c9 * pow2 (3 * 32) + uint_v c10 * pow2 (4* 32) + uint_v c11 * pow2 (5 * 32) + uint_v c13 * pow2 (7 * 32)})


let fast_reduction_upload_eighth_buffer input = 
    let (c8, c9, c10, c11, c12, c13, c14, c15) = input in 
    let b0 = store_high_low_u c15 c14 in 
    let b1 = store_high_low_u c9 (u32 0) in 
    let b2 = store_high_low_u c11 c10 in 
    let b3 = store_high_low_u c13 (u32 0) in 
     assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
     assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
     assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
     assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
     assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));    
    (b0, b1, b2, b3)


private 
val lemma_mod_add_distr (a:int) (b:int) (n:pos) : Lemma ((a + b % n) % n = (a + b) % n)
let lemma_mod_add_distr (a:int) (b:int) (n:pos) =
  lemma_div_mod b n;
  lemma_mod_plus (a + (b % n)) (b / n) n

private
val lemma_mod_sub_distr (a:int) (b:int) (n:pos) : Lemma ((a - b % n) % n = (a - b) % n)
let lemma_mod_sub_distr (a:int) (b:int) (n:pos) =
  lemma_div_mod b n;
  distributivity_sub_left 0 (b / n) n;
  lemma_mod_plus (a - (b % n)) (-(b / n)) n 


private val lemma_mod_twice : a:int -> p:pos -> Lemma ((a % p) % p == a % p)
private let lemma_mod_twice a p = lemma_mod_mod (a % p) a p

val reduce_brackets: r_0: nat -> r_1: nat -> r_2: nat -> r_3: nat -> r_4: nat -> r_5: nat -> r_6: nat -> r_7: nat -> r_8: nat ->  
  Lemma (ensures (((((((((r_0 + 2 * r_1 % prime) % prime + 2 * r_2 % prime) % prime + r_3) % prime + r_4) % prime - r_5) % prime - r_6) % prime - r_7) % prime - r_8) % prime == (r_0 + 2 * r_1 + 2* r_2 + r_3 + r_4 - r_5 - r_6 - r_7 - r_8) % prime))

let reduce_brackets r_0 r_1 r_2 r_3 r_4 r_5 r_6 r_7 r_8 = 
  lemma_mod_add_distr r_0 (2 * r_1) prime;
  modulo_distributivity (r_0 + 2 * r_1) (2 * r_2) prime;
  lemma_mod_add_distr r_3 (r_0 + 2 * r_1 + 2 * r_2) prime;
  lemma_mod_add_distr r_4  (r_0 + 2 * r_1 + 2 * r_2 + r_3) prime;

  modulo_distributivity ((r_0 + 2 * r_1 + 2 * r_2 + r_3 + r_4) % prime) (-r_5) prime;
  lemma_mod_twice (r_0 + 2 * r_1 + 2 * r_2 + r_3 + r_4) prime;
  modulo_distributivity (r_0 + 2 * r_1 + 2 * r_2 + r_3 + r_4) (-r_5) prime;

  modulo_distributivity ((r_0 + 2 * r_1 + 2 * r_2 + r_3 + r_4 - r_5) % prime) (-r_6) prime;
  lemma_mod_twice (r_0 + 2 * r_1 + 2 * r_2 + r_3 + r_4 - r_5) prime;
  modulo_distributivity (r_0 + 2 * r_1 + 2 * r_2 + r_3 + r_4 - r_5) (- r_6) prime;

  modulo_distributivity ((r_0 + 2 * r_1 + 2 * r_2 + r_3 + r_4 - r_5 -r_6) % prime) (-r_7) prime;
  lemma_mod_twice (r_0 + 2 * r_1 + 2 * r_2 + r_3 + r_4 - r_5 -r_6) prime;
  modulo_distributivity (r_0 + 2 * r_1 + 2 * r_2 + r_3 + r_4 - r_5 -r_6) (-r_7) prime;

  modulo_distributivity ((r_0 + 2 * r_1 + 2 * r_2 + r_3 + r_4 - r_5 -r_6 - r_7) % prime) (-r_8) prime;
  lemma_mod_twice(r_0 + 2 * r_1 + 2 * r_2 + r_3 + r_4 - r_5 -r_6 - r_7) prime;
  modulo_distributivity (r_0 + 2 * r_1 + 2 * r_2 + r_3 + r_4 - r_5 -r_6 -r_7) (-r_8) prime
 

val mult_two_replace: 
c11_n : nat  -> 
c12_n : nat  ->
c13_n : nat  -> 
c14_n : nat  -> 
c15_n : nat  -> 
Lemma (2 * (c11_n * pow2 (3 * 32) + c12_n * pow2 (4 * 32) + c13_n * pow2 (5 * 32) + c14_n * pow2 (6 * 32) + c15_n * pow2 (7 * 32)) == 2 * c11_n * pow2 (3 * 32) + 2 * c12_n * pow2 (4 * 32) + 2 * c13_n * pow2 (5 * 32) + 2* c14_n * pow2 (6 * 32) + 2 * c15_n * pow2 (7 * 32))


let mult_two_replace c11 c12 c13 c14 c15 = ()

val mult_two_replace_4:
c12_n : nat ->
c13_n : nat -> 
c14_n : nat -> 
c15_n : nat-> 
Lemma (2 * (c12_n * pow2 (3 * 32) + c13_n * pow2 (4 * 32) + c14_n * pow2 (5 * 32) + c15_n * pow2 (6 * 32)) ==
2 * c12_n * pow2 (3 * 32) + 2 * c13_n * pow2 (4 * 32) + 2* c14_n * pow2 (5 * 32) + 2 * c15_n * pow2 (6 * 32))


let mult_two_replace_4 c12 c13 c14 c15 = ()


val lemma_equivalence_eight_parts: 
  c0_n : int-> c1_n: int -> c2_n: int -> c3_n: int -> c4_n : int -> c5_n : int -> c6_n: int -> c7_n: int -> c8_n:int ->
  d0_n : int{d0_n == c0_n} -> d1_n: int{d1_n == c1_n} -> d2_n: int{d2_n == c2_n} -> d3_n: int{d3_n == c3_n} -> d4_n : int{d4_n == c4_n} -> d5_n : int{d5_n == c5_n} -> d6_n: int{d6_n == c6_n} -> d7_n: int{d7_n == c7_n} -> d8_n:int{d8_n == c8_n} ->
  a: int {a == (c0_n + c1_n + c2_n + c3_n + c4_n - c5_n - c6_n - c7_n - c8_n) % prime} -> 
  Lemma (a == (d0_n + d1_n + d2_n + d3_n + d4_n - d5_n - d6_n - d7_n - d8_n) % prime)  

let lemma_equivalence_eight_parts c0 c1 c2 c3 c4 c5 c6 c7 c8 d0 d1 d2 d3 d4 d5 d6 d7 d8 a = ()


val sometimes_fstar_could_not_prove_strange_things: 
  c0_n : nat -> c1_n: nat -> c2_n: nat -> c3_n: nat -> c4_n : nat -> c5_n : nat -> c6_n: nat -> c7_n: nat -> c8_n: nat -> c9_n : nat -> c10_n: nat -> c11_n: nat -> c12_n: nat -> c13_n: nat -> c14_n: nat -> c15_n: nat -> 
  r0:nat{r0 = c0_n + c1_n * pow2 (1 * 32) + c2_n * pow2 (2 * 32) + c3_n * pow2 (3 * 32) + c4_n * pow2 (4 * 32) + c5_n * pow2 (5 * 32) + c6_n * pow2 (6 * 32) + c7_n * pow2 (7 * 32)} ->
  r1:nat{r1 = c11_n * pow2 (3 * 32) + c12_n * pow2 (4 * 32) + c13_n * pow2 (5 * 32) +  c14_n * pow2 (6 * 32) + c15_n * pow2 (7 * 32)} -> 
  r2:nat{r2 = c12_n * pow2 (3 * 32) + c13_n * pow2 (4 * 32) + c14_n * pow2 (5* 32) + c15_n * pow2 (6 * 32)} ->  
  r3:nat{r3 = c8_n + c9_n * pow2 32 + c10_n * pow2 (2 * 32) + c14_n * pow2 (6 * 32) + c15_n * pow2 (7 * 32)} -> 
  r4:nat{r4 = c9_n + c10_n * pow2 32 + c11_n * pow2 (2 * 32) + c13_n * pow2 (3 * 32) + c14_n * pow2 (4 * 32) + c15_n * pow2 (5 * 32) + c13_n * pow2 (6 * 32) + c8_n * pow2 (7 * 32)} -> 
  r5:nat{r5 = c11_n + c12_n * pow2 32 + c13_n * pow2 (2 * 32) + c8_n * pow2 (6 * 32) + c10_n * pow2 (7 * 32)} -> 
  r6:nat{r6 = c12_n + c13_n * pow2 32 + c14_n * pow2 (2 * 32) + c15_n * pow2 (3 * 32) + c9_n * pow2 (6 * 32) + c11_n * pow2 (7 * 32)} -> 
  r7:nat{r7 = c13_n + c14_n * pow2 32 + c15_n * pow2 (2 * 32) + c8_n * pow2 (3* 32) + c9_n * pow2 (4 * 32) + c10_n * pow2 (5 * 32) + c12_n * pow2 (7 * 32)} -> 
  r8:nat{r8 = c14_n + c15_n * pow2 32 + c9_n * pow2 (3 * 32) + c10_n * pow2 (4* 32) +  c11_n * pow2 (5 * 32) + c13_n * pow2 (7 * 32)} -> 
  resultBefore: nat {resultBefore = (r0 + 2 * r1 + 2 * r2 + r3 + r4 - r5 - r6 - r7- r8) % prime} ->
  Lemma (resultBefore = (c0_n + c1_n * pow2 32 + c2_n * pow2 (2 * 32) + c3_n * pow2 (3 * 32) + c4_n * pow2 (4 * 32) + c5_n * pow2 (5 * 32) + c6_n * pow2 (6 * 32) + c7_n * pow2 (7 * 32) + 
    2 * c11_n * pow2 (3 * 32) + 2 * c12_n * pow2 (4 * 32) + 2 * c13_n * pow2 (5* 32) + 2* c14_n * pow2 (6 * 32) + 2 * c15_n * pow2 (7 * 32) + 
    2 * c12_n * pow2 (3 * 32) + 2 * c13_n * pow2 (4 * 32) + 2 * c14_n * pow2 (5* 32) + 2* c15_n * pow2 (6 * 32) + 
    c8_n + c9_n * pow2 32 + c10_n * pow2 (2 * 32) + c14_n * pow2 (6 * 32) +  c15_n * pow2 (7 * 32) + 
    c9_n + c10_n * pow2 32 + c11_n * pow2 (2 * 32) + c13_n * pow2 (3 * 32) + c14_n * pow2 (4 * 32) + c15_n * pow2 (5 * 32) + c13_n * pow2 (6 * 32) + c8_n * pow2 (7 * 32) 
     - c11_n - c12_n * pow2 32 - c13_n * pow2 (2 * 32) - c8_n * pow2 (6 * 32) - c10_n * pow2 (7 * 32) 
     - c12_n - c13_n * pow2 32 - c14_n * pow2 (2 * 32) - c15_n * pow2 (3 * 32) - c9_n * pow2 (6 * 32) - c11_n * pow2 (7 * 32) 
     - c13_n - c14_n * pow2 32 - c15_n * pow2 (2 * 32) - c8_n * pow2 (3* 32) - c9_n * pow2 (4 * 32) - c10_n * pow2 (5 * 32) - c12_n * pow2 (7 * 32) 
     - c14_n - c15_n * pow2 32 - c9_n * pow2 (3 * 32) - c10_n * pow2 (4* 32) - c11_n * pow2 (5 * 32) - c13_n * pow2 (7 * 32)) % prime)


let sometimes_fstar_could_not_prove_strange_things c0_n c1_n c2_n c3_n c4_n c5_n c6_n c7_n c8_n c9_n c10_n c11_n c12_n c13_n c14_n c15_n r0 r1 r2 r3 r4 r5 r6 r7 r8 resultBefore = 
  let p0 = c0_n + c1_n * pow2 (1 * 32) + c2_n * pow2 (2 * 32) + c3_n * pow2 (3 * 32) + c4_n * pow2 (4 * 32) + c5_n * pow2 (5 * 32) + c6_n * pow2 (6 * 32) + c7_n * pow2 (7 * 32) in 
  let p1 = 2 * (c11_n * pow2 (3 * 32) + c12_n * pow2 (4 * 32) + c13_n * pow2 (5 * 32) +  c14_n * pow2 (6 * 32) + c15_n * pow2 (7 * 32)) in
  let p2 = 2 * (c12_n * pow2 (3 * 32) + c13_n * pow2 (4 * 32) + c14_n * pow2 (5* 32) + c15_n * pow2 (6 * 32)) in 
  let p3 = c8_n + c9_n * pow2 32 + c10_n * pow2 (2 * 32) + c14_n * pow2 (6 * 32) +  c15_n * pow2 (7 * 32) in 
  let p4 = c9_n + c10_n * pow2 32 + c11_n * pow2 (2 * 32) + c13_n * pow2 (3 * 32) + c14_n * pow2 (4 * 32) + c15_n * pow2 (5 * 32) + c13_n * pow2 (6 * 32) + c8_n * pow2 (7 * 32) in
  let p5 = c11_n + c12_n * pow2 32 + c13_n * pow2 (2 * 32) + c8_n * pow2 (6 * 32) + c10_n * pow2 (7 * 32) in 
  let p6 = c12_n + c13_n * pow2 32 + c14_n * pow2 (2 * 32) + c15_n * pow2 (3 * 32) + c9_n * pow2 (6 * 32) + c11_n * pow2 (7 * 32)  in 
  let p7 = c13_n + c14_n * pow2 32 + c15_n * pow2 (2 * 32) + c8_n * pow2 (3* 32) + c9_n * pow2 (4 * 32) + c10_n * pow2 (5 * 32) + c12_n * pow2 (7 * 32)  in 
  let p8 = c14_n + c15_n * pow2 32 + c9_n * pow2 (3 * 32) + c10_n * pow2 (4* 32) + c11_n * pow2 (5 * 32) + c13_n * pow2 (7 * 32) in 
  
  lemma_equivalence_eight_parts r0 (2 * r1) (2*r2) r3 r4 r5 r6 r7 r8 p0 p1 p2 p3 p4 p5 p6 p7 p8 resultBefore;
  
  mult_two_replace c11_n c12_n c13_n c14_n c15_n;
  mult_two_replace_4 c12_n c13_n c14_n c15_n
  
#reset-options " --z3rlimit 200"

let solinas_reduction f = 
  let (f0, f1, f2, f3, f4, f5, f6, f7)  = f in
    assert_norm (pow2 64 * pow2 64 = pow2 (2 * 64));
    assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 (3 * 64));
    assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 (4 * 64));
    assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 (5 * 64));
    assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64  = pow2 (6 * 64));
    assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 (7 * 64));

    assert(D.wide_as_nat4 f = uint_v f0 + uint_v f1 * pow2 64 + uint_v f2 * pow2 (2 * 64) + uint_v f3 * pow2 (3 * 64) + 
    uint_v f4 * pow2 (4 * 64) + uint_v  f5 * pow2 (5 * 64) + uint_v f6*pow2 (6 * 64) + uint_v f7 * pow2 (7 * 64));
    
  let c0 = get_low_part f0 in 
  [@inline_let]
    let c0_n: nat = uint_v c0 in 
  let c1 = get_high_part f0 in 
  [@inline_let]
    let c1_n:nat = uint_v c1 in 
  let c2 = get_low_part f1 in
  [@inline_let]
    let c2_n:nat = uint_v c2 in 
  let c3 = get_high_part f1 in
  [@inline_let]
    let c3_n:nat = uint_v c3 in 
  let c4 = get_low_part f2 in
  [@inline_let]
    let c4_n:nat = uint_v c4 in 
  let c5 = get_high_part f2 in
  [@inline_let]
    let c5_n:nat = uint_v c5 in 
  let c6 = get_low_part f3 in
  [@inline_let]
    let c6_n:nat = uint_v c6 in 
  let c7 = get_high_part f3 in
  [@inline_let]
    let c7_n:nat = uint_v c7 in 

  let c8 = get_low_part f4 in 
  [@inline_let]
    let (c8_n:nat{c8_n < pow2 32}) = uint_v c8 in 
  let c9 = get_high_part f4 in
  [@inline_let]
    let (c9_n:nat{c9_n < pow2 32}) = uint_v c9 in
  let c10 = get_low_part f5 in   
  [@inline_let]
    let (c10_n:nat{c10_n < pow2 32}) = uint_v c10 in 
  let c11 = get_high_part f5 in
  [@inline_let]
    let (c11_n:nat{c11_n< pow2 32})  = uint_v c11 in 
  let c12 = get_low_part f6 in 
  [@inline_let]
    let (c12_n:nat{c12_n < pow2 32}) = uint_v c12 in 
  let c13 = get_high_part f6 in
  [@inline_let]
    let (c13_n:nat{c13_n < pow2 32}) = uint_v c13 in 
  let c14 = get_low_part  f7 in
  [@inline_let]
    let (c14_n:nat{c14_n < pow2 32}) = uint_v c14 in 
  let c15 = get_high_part f7 in
  [@inline_let]
    let (c15_n:nat{c15_n < pow2 32}) = uint_v c15 in 

  assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
  assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
  assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
  assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
  assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));
  assert_norm (pow2 (6 * 32) * pow2 (2 * 32) = pow2 (8 * 32));
  assert_norm (pow2 (7 * 32) * pow2 (2 * 32) = pow2 (9 * 32));
  assert_norm (pow2 (8 * 32) * pow2 (2 * 32) = pow2 (10 * 32));
  assert_norm (pow2 (9 * 32) * pow2 (2 * 32) = pow2 (11 * 32));
  assert_norm (pow2 (10 * 32) * pow2 (2 * 32) = pow2 (12 * 32));
  assert_norm (pow2 (11 * 32) * pow2 (2 * 32) = pow2 (13 * 32));
  assert_norm (pow2 (12 * 32) * pow2 (2 * 32) = pow2 (14 * 32));
  assert_norm (pow2 (13 * 32) * pow2 (2 * 32) = pow2 (15 * 32));


  assert(D.wide_as_nat4 f =  (c0_n + c1_n * pow2 32 + c2_n * pow2 (2 * 32) + c3_n * pow2 (3 * 32) + c4_n * pow2 (4 * 32) + c5_n * pow2 (5 * 32) + c6_n * pow2 (6 * 32) + c7_n * pow2 (7 * 32) + c8_n * pow2 256 + c9_n * pow2 288 + c10_n * pow2 (10 * 32)  + c11_n * pow2 (11 * 32) + c12_n * pow2 (12 * 32) + c13_n* pow2 (13 * 32) + c14_n * pow2 (14 * 32) + c15_n * pow2 (15 * 32)));

  let c_low = (c0, c1, c2, c3, c4, c5, c6, c7) in 
  let c_high = (c8, c9, c10, c11, c12, c13, c14, c15) in 

  let state0 = fast_reduction_upload_zero_buffer  c_low in 
    let state0_red = reduction_prime_2prime state0 in 
  let state1 = fast_reduction_upload_first_buffer c_high in 
  let state2 = fast_reduction_upload_second_buffer c_high in 
  let state3 = fast_reduction_upload_third_buffer c_high in 
      let state3_red = reduction_prime_2prime state3 in  
  let state4 = fast_reduction_upload_forth_buffer c_high in 
      let state4_red = reduction_prime_2prime state4 in 
  let state5 = fast_reduction_upload_fifth_buffer c_high in 
      let state5_red = reduction_prime_2prime state5 in     
  let state6 = fast_reduction_upload_sixth_buffer c_high in 
    let state6_red = reduction_prime_2prime state6 in 
  let state7 = fast_reduction_upload_seventh_buffer c_high in 
      let state7_red = reduction_prime_2prime state7 in 
  let state8 = fast_reduction_upload_eighth_buffer c_high in 
      let state8_red = reduction_prime_2prime state8 in 

  let state1_2 = shift_left_felem state1 in 
  let state2_2 = shift_left_felem state2 in 

  let r0 = felem_add state0_red state1_2 in 
    lemma_mod_add_distr (D.as_nat4 state1_2) (D.as_nat4 state0) prime;
  let r1 = felem_add r0 state2_2 in 
  let r0 = felem_add r1 state3_red in 
    lemma_mod_add_distr (D.as_nat4 r1) (D.as_nat4 state3) prime;
  let r1 = felem_add r0 state4_red in 
    lemma_mod_add_distr (D.as_nat4 r0) (D.as_nat4 state4) prime;
  let r0 = felem_sub r1 state5_red in 
    lemma_mod_sub_distr (D.as_nat4 r1) (D.as_nat4 state5) prime;
  let r1 = felem_sub r0 state6_red in 
    lemma_mod_sub_distr (D.as_nat4 r0) (D.as_nat4 state6) prime;
  let r0 = felem_sub r1 state7_red in 
    lemma_mod_sub_distr (D.as_nat4 r1) (D.as_nat4 state7) prime;
  let result = felem_sub r0 state8_red in 
    lemma_mod_sub_distr (D.as_nat4 r0) (D.as_nat4 state8) prime;

    assert(D.as_nat4 result = ((((((((((D.as_nat4 state0 + (D.as_nat4 state1 * 2) % prime) % prime + (D.as_nat4 state2 * 2) % prime) % prime + D.as_nat4 state3) % prime) + D.as_nat4 state4) % prime - D.as_nat4 state5) % prime) - D.as_nat4 state6) % prime - D.as_nat4 state7) % prime - D.as_nat4 state8) % prime);

    reduce_brackets (D.as_nat4 state0) (D.as_nat4 state1) (D.as_nat4 state2) (D.as_nat4 state3) (D.as_nat4 state4) (D.as_nat4 state5) (D.as_nat4 state6) (D.as_nat4 state7) (D.as_nat4 state8);
    
  (*assert(D.as_nat4 result = (D.as_nat4 state0 + 2 * D.as_nat4 state1 + 2 * D.as_nat4 state2 + D.as_nat4 state3 + D.as_nat4 state4 - D.as_nat4 state5 - D.as_nat4 state6 - D.as_nat4 state7 - D.as_nat4 state8) % prime);*)


  sometimes_fstar_could_not_prove_strange_things c0_n c1_n c2_n c3_n c4_n c5_n c6_n c7_n c8_n c9_n c10_n c11_n c12_n c13_n c14_n c15_n (D.as_nat4 state0) (D.as_nat4 state1) (D.as_nat4 state2) (D.as_nat4 state3) (D.as_nat4 state4) (D.as_nat4 state5) (D.as_nat4 state6) (D.as_nat4 state7) (D.as_nat4 state8) (D.as_nat4 result);

  (*assert(D.as_nat4 result = (
  c0_n + c1_n * pow2 32 + c2_n * pow2 (2 * 32) + c3_n * pow2 (3 * 32) + c4_n * pow2 (4 * 32) + c5_n * pow2 (5 * 32) + c6_n * pow2 (6 * 32) + c7_n * pow2 (7 * 32) + 
  2 * c11_n * pow2 (3 * 32) + 2 * c12_n * pow2 (4 * 32) + 2 * c13_n * pow2 (5* 32) + 2* c14_n * pow2 (6 * 32) + 2 * c15_n * pow2 (7 * 32) + 
  2 * c12_n * pow2 (3 * 32) + 2 * c13_n * pow2 (4 * 32) + 2 * c14_n * pow2 (5* 32) + 2* c15_n * pow2 (6 * 32) + c8_n + c9_n * pow2 32 + c10_n * pow2 (2 * 32) + c14_n * pow2 (6 * 32) +  c15_n * pow2 (7 * 32) + 
  c9_n + c10_n * pow2 32 + c11_n * pow2 (2 * 32) + c13_n * pow2 (3 * 32) + c14_n * pow2 (4 * 32) + c15_n * pow2 (5 * 32) + c13_n * pow2 (6 * 32) + c8_n * pow2 (7 * 32) 
  - c11_n - c12_n * pow2 32 - c13_n * pow2 (2 * 32) - c8_n * pow2 (6 * 32) - c10_n * pow2 (7 * 32) 
  - c12_n - c13_n * pow2 32 - c14_n * pow2 (2 * 32) - c15_n * pow2 (3 * 32) - c9_n * pow2 (6 * 32) - c11_n * pow2 (7 * 32)
  - c13_n - c14_n * pow2 32 - c15_n * pow2 (2 * 32) - c8_n * pow2 (3* 32) - c9_n * pow2 (4 * 32) - c10_n * pow2 (5 * 32) - c12_n * pow2 (7 * 32)
  - c14_n - c15_n * pow2 32 - c9_n * pow2 (3 * 32) - c10_n * pow2 (4* 32) - c11_n * pow2 (5 * 32) - c13_n * pow2 (7 * 32)) % prime);*)

 [@inline_let]
 let bn = 
 c0_n + c1_n * pow2 32 + c2_n * pow2 (2 * 32) + c3_n * pow2 (3 * 32) + c4_n * pow2 (4 * 32) + c5_n * pow2 (5 * 32) + c6_n * pow2 (6 * 32) + c7_n * pow2 (7 * 32) +
 2 * c11_n * pow2 (3 * 32) + 2 * c12_n * pow2 (4 * 32) + 2 * c13_n * pow2 (5* 32) + 2* c14_n * pow2 (6 * 32) + 2 * c15_n * pow2 (7 * 32) + 
 2 * c12_n * pow2 (3 * 32) + 2 * c13_n * pow2 (4 * 32) + 2 * c14_n * pow2 (5* 32) + 2* c15_n * pow2 (6 * 32) +
 c8_n + c9_n * pow2 32 + c10_n * pow2 (2 * 32) + c14_n * pow2 (6 * 32) +  c15_n * pow2 (7 * 32) + 
 c9_n + c10_n * pow2 32 + c11_n * pow2 (2 * 32) + c13_n * pow2 (3 * 32) + c14_n * pow2 (4 * 32) + c15_n * pow2 (5 * 32) + c13_n * pow2 (6 * 32) + c8_n * pow2 (7 * 32)  
 - c11_n - c12_n * pow2 32 - c13_n * pow2 (2 * 32) - c8_n * pow2 (6 * 32) - c10_n * pow2 (7 * 32)
 - c12_n - c13_n * pow2 32 - c14_n * pow2 (2 * 32) - c15_n * pow2 (3 * 32) - c9_n * pow2 (6 * 32) - c11_n * pow2 (7 * 32)
 - c13_n - c14_n * pow2 32 - c15_n * pow2 (2 * 32) - c8_n * pow2 (3* 32) - c9_n * pow2 (4 * 32) - c10_n * pow2 (5 * 32) - c12_n * pow2 (7 * 32) 
 - c14_n - c15_n * pow2 32 - c9_n * pow2 (3 * 32) - c10_n * pow2 (4* 32) - c11_n * pow2 (5 * 32) - c13_n * pow2 (7 * 32) in 

solaris_reduction c0_n c1_n c2_n c3_n c4_n c5_n c6_n c7_n c8_n c9_n c10_n c11_n c12_n c13_n c14_n c15_n bn;

 result

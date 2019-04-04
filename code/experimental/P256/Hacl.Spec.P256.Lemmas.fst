module Hacl.Spec.P256.Lemmas

open Lib.IntTypes
open FStar.Math.Lemmas
open FStar.Math.Lib
open Hacl.Spec.Curve25519.Field64.Definition
open  Hacl.Spec.Curve25519.Field64.Core

open FStar.Mul

open Hacl.Spec.P256.Definitions

val p256_prime_value: n : nat ->  Lemma
	(requires (n = 256))
	(ensures (pow2 n - pow2 224 + pow2 192 + pow2 96 -1 = 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff))
	[SMTPat (pow2 n - pow2 224 + pow2 192 + pow2 96 - 1)]

let p256_prime_value n = 
	assert_norm(pow2 256 - pow2 224 + pow2 192 + pow2 96 - 1 = 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff)


assume val log_and: a: uint64 -> b: uint64{uint_v b == 0 \/ uint_v b == pow2 64 - 1} -> 
Lemma (if uint_v b = 0 then uint_v (logand a b) == 0 else uint_v (logand a b) == uint_v a)

assume val log_or: a: uint64 -> b: uint64 {uint_v b == 0 \/ uint_v a == 0} -> 
Lemma (if uint_v b = 0 then uint_v (logor a b) == uint_v a else uint_v (logor a b) == uint_v b)

assume val log_not_lemma: b: uint64{uint_v b == 0 \/ uint_v b == pow2 64 - 1} -> 
Lemma(if uint_v b = 0 then uint_v (lognot (b)) == pow2 64 -1 else uint_v (lognot b) == 0)


val lemma_nat_4: f: felem4 -> Lemma (as_nat4 f < pow2 256)

let lemma_nat_4 f = 
  let (s0, s1, s2, s3) = f in 
  let r_n = as_nat4 f in 
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
  a: felem4 {as_nat4 a < prime} -> 
  b: felem4 {as_nat4 b < prime} -> 
  Lemma (ensures (
let p256 = (u64 0xffffffffffffffff, u64 0xffffffff, u64 0, u64 0xffffffff00000001) in 
let (x8, c) = add4 a b in 
let (x16, r) = sub4 c p256 in 
uint_v x8 == 1 ==> uint_v x16 == 1))

let lemma_for_multiplication_1 a b = 
  let p256 = (u64 0xffffffffffffffff, u64 0xffffffff, u64 0, u64 0xffffffff00000001) in 
  assert_norm(prime < pow2 256);
  assert_norm(as_nat4 p256 == prime);
  let (x8, c) = add4 a b in 
  let (x16, r) = sub4 c p256 in   
  admit();
  lemma_nat_4 c

val small_modulo_lemma_extended: a: nat -> b: pos -> Lemma (if a < b then a % b = a else True)

let small_modulo_lemma_extended a b = 
  if a < b then 
    small_modulo_lemma_1 a b



val lemma_add4_zero: a: felem4 -> b: felem4 -> Lemma (let (c, r) = add4 a b in 
  if as_nat4 a = 0 then uint_v c == 0 /\ as_nat4 r == as_nat4 b 
  else if as_nat4 b = 0 then uint_v c == 0 /\ as_nat4 r == as_nat4 a 
  else True)

let lemma_add4_zero a b = ()
  
val lemma_adding_prime: a: felem4{as_nat4 a < prime}  -> b: felem4{as_nat4 b < prime} -> Lemma (let (c, r) = sub4 a b in 
  if as_nat4 a < as_nat4 b then 
    (as_nat4 a - as_nat4 b) % prime == (as_nat4 r - pow2 256 + prime) 
  else
     (as_nat4 a - as_nat4 b) % prime == as_nat4 r)

let lemma_adding_prime a b = 
  let (c, r) = sub4 a b in 
  if as_nat4 a < as_nat4 b then 
    begin 
      let result = as_nat4 r - pow2 256 in 
      small_modulo_lemma_extended (result + prime) prime;
      modulo_addition_lemma result prime 1
      end
  else
    begin
      small_modulo_lemma_extended (as_nat4 r) prime
    end

val lemma_enough_to_carry: a: felem4 -> b: felem4 -> Lemma (
  if as_nat4 b >= (pow2 256 - as_nat4 a) then 
    let (c, r) = add4 a b in 
    uint_v c == 1
    else True)
    
let lemma_enough_to_carry a b = 
 if as_nat4 b >= (pow2 256 - as_nat4 a) then begin
  let (c, r) = add4 a b in 
    lemma_nat_4 r
  end
  else
  ()


val lemma_sub_add: a: felem4 -> b:felem4 ->
  prime_temp: felem4{if as_nat4 a < as_nat4 b then as_nat4 prime_temp == prime else as_nat4 prime_temp == 0} ->  
  r: felem4{if as_nat4 a < as_nat4 b then (as_nat4 a - as_nat4 b) % prime ==
    (as_nat4 r - pow2 256 + prime) else (as_nat4 a - as_nat4 b) % prime == as_nat4 r} -> 
 Lemma(let (c, r1) = add4 prime_temp r in (as_nat4 a - as_nat4 b) % prime == as_nat4 r1)

let lemma_sub_add a b prime_temp r = 
  if as_nat4 a >= as_nat4 b then ()
  else
    begin
      let result = as_nat4 r - pow2 256 + prime in 
      let (c, r1) = add4 prime_temp r in 
      lemma_enough_to_carry prime_temp r
    end


val equal_plus_minus : a: felem4 -> b: nat -> Lemma (as_nat4 a + b - b == as_nat4 a)

let equal_plus_minus a b = ()



let ( +% ) a b = (a + b) % prime
let ( -% ) a b = (a - b) % prime
let ( *% ) a b = (a * b) % prime


val ( **% ) : e: nat -> n: nat{n > 0} -> Tot (r: nat) (decreases n)

let rec ( **% ) e n =
  if n = 1 then e
  else
    if n % 2 = 0 then 
    begin
     	(e *% e) **% (n / 2)
    end
    else e *% ((e *% e) **% ((n-1)/2))


let modp_inv (x: nat {x < prime}) : Tot (r: nat{r < prime}) = 
	(x **% (prime - 2)) % prime


let modp_inv2 (x: nat) : Tot (r: nat {r < prime}) = 
  assert_norm (prime > 0);
  let r = x % prime in 
  modp_inv r


#reset-options "--max_fuel 0 --z3rlimit 100" 


val modulo_distributivity_mult: a: int -> b: int -> c: pos -> Lemma ((a * b) % c = ((a % c) * (b % c)) % c)

let modulo_distributivity_mult a b c = 
  lemma_mod_mul_distr_l a b c;
  lemma_mod_mul_distr_r (a%c) b c


val modulo_distributivity_mult_last_two: a: int -> b: int -> c: int -> d: int -> e: int -> f: pos -> Lemma ((a * b * c * d * e) % f = (a * b * c * (d * e % f)) % f)

let modulo_distributivity_mult_last_two a b c d e f = admit()


#reset-options "--max_fuel 0 --z3rlimit 100" 

private val lemma_mod_twice : a:int -> p:pos -> Lemma ((a % p) % p == a % p)
private let lemma_mod_twice a p = lemma_mod_mod (a % p) a p

val lemma_multiplication_to_same_number: a: nat -> b: nat ->c: nat ->  
  Lemma (requires (a % prime = b % prime)) (ensures ((a * c) % prime = (b * c) % prime))

let lemma_multiplication_to_same_number a b c = 
  lemma_mod_mul_distr_l a c prime;
  lemma_mod_mul_distr_l b c prime

val lemma_division_is_multiplication: t3: nat{ exists (k: nat) . k * pow2 64 = t3} -> Lemma (ensures (t3 * modp_inv2 (pow2 64) % prime = (t3 / pow2 64) % prime))

let lemma_division_is_multiplication t3 =  
  let t_new = t3 * modp_inv2 (pow2 64) % prime in 
  let remainder = t3 / pow2 64 in 
  assert_norm(modp_inv2 (pow2 64) * pow2 64 % prime = 1);
  modulo_distributivity_mult remainder (modp_inv2 (pow2 64) * pow2 64) prime;
  lemma_mod_twice remainder prime;

  ()

val mult_one_round: t: nat -> co: nat{t % prime == co% prime}  -> Lemma
(requires True)
(ensures (let result = (t + (t % pow2 64) * prime) / pow2 64 % prime in result == (co * modp_inv2 (pow2 64)) % prime))

let mult_one_round t co = 
    let t1 = t % pow2 64 in 
    let t2 = t1 * prime in 
    let t3 = t + t2 in 
      assert(t3 % prime = co % prime);
    let t = t3 / pow2 64 in 
      assert(let rem = t3/ pow2 64 in rem * pow2 64 = t3);
      assert(exists (k: nat). k * pow2 64 = t3);
      lemma_division_is_multiplication t3;
      lemma_multiplication_to_same_number t3 co (modp_inv2 (pow2 64))

val lemma_m: a: nat -> b: nat -> c: nat {b == c} -> Lemma (a * b = a * c)

let lemma_m a b c = ()

val lemma_decrease_pow: a: nat -> Lemma (ensures (a * modp_inv2 (pow2 64) * modp_inv2 (pow2 64) * modp_inv2 (pow2 64) * modp_inv2 (pow2 64))  % prime == (a * modp_inv2 (pow2 256)) % prime) 

let lemma_decrease_pow a = 
  assert_norm(modp_inv2 (pow2 64) = 6277101733925179126845168871924920046849447032244165148672);
  assert_norm(pow2 256 = 115792089237316195423570985008687907853269984665640564039457584007913129639936);
  assert_norm(modp_inv2 (pow2 256) =115792089183396302114378112356516095823261736990586219612555396166510339686400 );
  assert((modp_inv2 (pow2 64) * modp_inv2 (pow2 64) * modp_inv2 (pow2 64) * modp_inv2(pow2 64))% prime  = (modp_inv2 (pow2 256)) % prime);

  lemma_mod_mul_distr_r a (modp_inv2 (pow2 64) * modp_inv2 (pow2 64) * modp_inv2 (pow2 64) * modp_inv2(pow2 64)) prime;
  lemma_mod_mul_distr_r a (modp_inv2 (pow2 256)) prime



val lemma_brackets : a: int -> b: int -> c: int -> Lemma (a * b * c = a * (b * c))

let lemma_brackets a b c = ()

val lemma_brackets_l: a: int -> b: int -> c: int -> Lemma (a * b * c = (a * b) * c)

let lemma_brackets_l a b c = ()

val lemma_brackets1: a: int -> b: int -> c: int -> Lemma (a * (b * c) = b * (a * c))

let lemma_brackets1 a b c = ()

val lemma_brackets5: a: nat -> b: nat -> c: nat -> d: nat -> e: nat -> Lemma (a * b * c * d * e = a * b * c * (d * e))

let lemma_brackets5 a b c d e = ()

val lemma_brackets5_twice: a: int -> b: int -> c: int -> d: int -> e: int -> Lemma (a * b * c * d * e = (a * d) * (b * e) * c)

let lemma_brackets5_twice a b c d e = admit()

val lemma_brackets7: a: int -> b: int -> c: int -> d: int -> e: int -> f: int -> g: int -> Lemma (a * b * c * d * e * f * g = a * b * c * d * e * (f * g))

let lemma_brackets7 a b c d e f g = admit()


val lemma_brackets7_twice: a: int -> b: int -> c: int -> d: int -> e: int -> f: int -> g: int -> Lemma (a * b * c * d * e * f * g = (a * e) * (b * f) * (c * g) * d)

let lemma_brackets7_twice a b c d e f g = admit()


val lemma_distr_mult3: a: int -> b: int -> c: int -> Lemma (a * b * c = a * c * b)

let lemma_distr_mult3 a b c = ()

val lemma_distr_mult : a: nat -> b: nat -> c: nat -> d: nat -> e: nat -> Lemma (a * b * c * d * e = a * b * d * c * e) 

let lemma_distr_mult a b c d e = ()

val lemma_twice_brackets: a: int -> b: int -> c: int -> d: int -> e: int -> f: int -> h: int-> Lemma 
  ((a * b * c) * (d * e * f) * h = a * b * c * d * e * f * h)

let lemma_twice_brackets a b c d e f h = () 

val lemma_distr_mult7: a: int -> b: int -> c: int -> d: int -> e: int -> f: int -> h: int-> Lemma 
  ( a * b * c * d * e * f * h = a * b * d * e * f * h * c)


val lemma_prime_as_wild_nat: a: felem8{wide_as_nat4 a < 2* prime} -> Lemma (let (t0, t1, t2, t3, t4, t5, t6, t7) = a in 
  uint_v t7 = 0 /\ uint_v t6 = 0 /\ uint_v t5 = 0 /\ (uint_v t4 = 0 \/ uint_v t4 = 1) /\
  as_nat4 (t0, t1, t2, t3) + uint_v t4 * pow2 256 = wide_as_nat4 a)

let lemma_prime_as_wild_nat a =
   assert_norm(pow2 64 * pow2 64 = pow2 128);
   assert_norm(pow2 64 * pow2 64 * pow2 64 = pow2 192);
   assert_norm(pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
   assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64= pow2 320);
   assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64 * pow2 64 = pow2 (6 * 64));
   assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64* pow2 64 * pow2 64 = pow2 (7 * 64))
  

val lemma_mul_nat2: a: nat -> b: nat -> Lemma (a * b >= 0)
let lemma_mul_nat2 a b = ()

val lemma_mul_nat: a:nat -> b:nat -> c: nat -> Lemma (a * b * c >= 0)
let lemma_mul_nat a b c = ()

val lemma_mul_nat4: a:nat -> b:nat -> c: nat -> d: nat -> Lemma (a * b * c * d >= 0)
let lemma_mul_nat4 a b c d = ()

val lemma_mul_nat5: a: nat -> b: nat -> c: nat -> d: nat -> e: nat -> Lemma (a * b * c * d * e >= 0)
let lemma_mul_nat5 a b c d e = ()



  

val modulo_distributivity_mult2: a: int -> b: int -> c: int -> d: pos -> Lemma (((a % d) * (b % d) * c) % d = (a * b * c)% d)

let modulo_distributivity_mult2 a b c d = 
  let start = ((a % d) * (b % d) * c) % d in 
  lemma_mod_mul_distr_l a ((b % d) * c) d;
  lemma_distr_mult3 a (b % d) c;
  lemma_mod_mul_distr_r (a * c) b d

assume val lemma_minus_distr (a: int) (b: int): Lemma ((a % prime - b % prime) % prime = (a - b)%prime)


val lemma_multiplication_not_mod_prime: a: nat{a < prime} -> b: nat {b > 0 /\ b % prime <> 0} -> 
  Lemma ((a * b) % prime == 0 <==> a == 0)

let lemma_multiplication_not_mod_prime a b = admit()

(*If k a ≡ k b (mod n) and k is coprime with n, then a ≡ b (mod n) *)

val lemma_modular_multiplication: a: nat  -> b: nat -> 
  n: pos -> k: pos {k % n <> 0} -> Lemma
  (requires  k * a % prime =  k * b % prime)
  (ensures a % prime == b % prime)


let lemma_modular_multiplication a b n k = admit()

val lemma_modular_multiplication_p256: a: nat{a < prime} -> b: nat{b < prime} -> 
  Lemma 
  (a * modp_inv2 (pow2 256) % prime = b * modp_inv2 (pow2 256) % prime  ==> a == b)

let lemma_modular_multiplication_p256 a b = admit()



val lemma_mod_sub_distr (a:int) (b:int) (n:pos) : Lemma ((a - b % n) % n = (a - b) % n)

let lemma_mod_sub_distr (a:int) (b:int) (n:pos) =
  lemma_div_mod b n;
  distributivity_sub_left 0 (b / n) n;
  // (a - b) % n == (a - (b % n) - (b / n) * n) % n
  lemma_mod_plus (a - (b % n)) (-(b / n)) n


val lemma_mod_add_distr (a:int) (b:int) (n:pos) : Lemma ((a + b % n) % n = (a + b) % n)
let lemma_mod_add_distr (a:int) (b:int) (n:pos) =
  lemma_div_mod b n;
  // (a + b) % n == (a + (b % n) + (b / n) * n) % n
  lemma_mod_plus (a + (b % n)) (b / n) n

val lemma_log_and1: a: uint64 {v a = 0 \/ v a = maxint U64} ->
  b: uint64 {v b = 0 \/ v b = maxint U64}  -> 
  Lemma (uint_v a = pow2 64 - 1 && uint_v b = pow2 64 - 1 <==> uint_v (logand a b) == pow2 64 - 1)

let lemma_log_and1 a b = 
  logand_lemma a b


val lemma_xor_copy_cond: a: uint64 -> b: uint64 -> mask: uint64{uint_v mask = 0 \/ uint_v mask = pow2 64 -1} ->
  Lemma(let r = logxor a (logand mask (logxor a b)) in 
  if uint_v mask = pow2 64 - 1 then r == b else r == a)

let lemma_xor_copy_cond a b mask = 
  let fst = logxor a b in 
  let snd = logand mask fst in 
    logand_lemma mask fst;
  let thrd = logxor a snd in    
    logxor_lemma a snd;
    logxor_lemma a b


val lognot_lemma: #t:inttype{~(U1? t)} -> a:uint_t t SEC -> Lemma
  (requires v a = 0 \/ v a = maxint t)
  (ensures (if v a = 0 then v (lognot a) == maxint t else v (lognot a) == 0)) 

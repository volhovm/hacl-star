module Hacl.Spec.P256.MontgomeryMultiplication.PointAdd

open Lib.IntTypes
open FStar.Math.Lemmas
open FStar.Math.Lib
open Hacl.Spec.P256.Lemmas
open Hacl.Spec.P256.Definitions
open Hacl.Spec.Curve25519.Field64.Definition
open Hacl.Spec.P256.Core
open Lib.Sequence
open Hacl.Impl.Curve25519.Field64.Core
open Hacl.Spec.P256.Core
open Hacl.Spec.P256.MontgomeryMultiplication
open Lib.Loops
open FStar.Mul

open Hacl.Spec.P256.MontgomeryMultiplication.PointDouble

#reset-options "--z3rlimit 300" 

noextract
let _point_add p q : point_nat = 
  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 

  let (x1, y1, z1) = p in
  let (x2, y2, z2) = q in 

  let z2z2 = z2 * z2 in 
  let z1z1 = z1 * z1 in 

  let u1 = x1 * z2z2 % prime in 
  let u2 = x2 * z1z1 % prime in 

  assert_by_tactic (x1 * z2 * z2 = x1 * (z2 * z2)) canon;
  assert_by_tactic (x2 * z1 * z1 = x2 * (z1 * z1)) canon;
  
  let s1 = y1 * z2 * z2z2 % prime in 
  let s2 = y2 * z1 * z1z1 % prime in

  assert_by_tactic (y1 * z2 * (z2 * z2) = y1 * z2 * z2 * z2) canon;
  assert_by_tactic (y2 * z1 * (z1 * z1) = y2 * z1 * z1 * z1) canon;

  if u1 = u2 && s1 = s2 && z1 <> 0 && z2 <> 0 then 
     _point_double (x1, y1, z1) 
  else 
    begin

      let h = (u2 - u1) % prime in 
      let r = (s2 - s1) % prime in

      let rr = (r * r)in 
      let hh = (h * h) in 
      let hhh = (h * h * h) in  

	assert_by_tactic (forall (n: nat). n * h * h = n * (h * h)) canon; 
	assert_by_tactic (s1 * (h * h * h) = s1 * h * h * h) canon;
      let x3 = (rr - hhh - 2 * u1 * hh) % prime in 
	assert(x3 = (r * r - h * h * h - 2 * u1 * h * h) % prime);
      let y3 = (r * (u1 * hh - x3) - s1 * hhh) % prime in
	assert(y3 = (r * (u1 * h*h - x3) - s1 * h*h*h) % prime);
      let z3 = (h * z1 * z2) % prime in
      if z2 = 0 then 
	(x1, y1, z1) 
      else if z1 = 0 then
	(x2, y2, z2) 
      else  
	(x3, y3, z3)
	
    end	


val move_from_jacobian_coordinates_lemma: p: point_prime -> q: point_prime -> Lemma (
  let x1 = Lib.Sequence.sub p 0 4 in 
  let y1 = Lib.Sequence.sub p 4 4 in 
  let z1 = Lib.Sequence.sub p 8 4 in 

  let x2 = Lib.Sequence.sub q 0 4 in 
  let y2 = Lib.Sequence.sub q 4 4 in 
  let z2 = Lib.Sequence.sub q 8 4 in 

  let z2Square = montgomery_multiplication_seq z2 z2 in 
  let z1Square = montgomery_multiplication_seq z1 z1 in 
  let z2Cube = montgomery_multiplication_seq z2Square z2 in 
  let z1Cube = montgomery_multiplication_seq z1Square z1 in 

  let u1 = montgomery_multiplication_seq x1 z2Square in 
  let u2 = montgomery_multiplication_seq x2 z1Square in 

  let s1 = montgomery_multiplication_seq y1 z2Cube in 
  let s2 = montgomery_multiplication_seq y2 z1Cube in 


  let x1D = fromDomain_ (felem_seq_as_nat x1) in 
  let y1D = fromDomain_ (felem_seq_as_nat y1) in 
  let z1D = fromDomain_ (felem_seq_as_nat z1) in 

  let x2D = fromDomain_ (felem_seq_as_nat x2) in 
  let y2D = fromDomain_ (felem_seq_as_nat y2) in 
  let z2D = fromDomain_ (felem_seq_as_nat z2) in 

  felem_seq_as_nat u1 == toDomain_ ((x1D * z2D * z2D) % prime)  /\
  felem_seq_as_nat u2 == toDomain_ ((x2D * z1D * z1D) % prime) /\
  felem_seq_as_nat s1 == toDomain_ ((y1D * z2D * z2D * z2D) % prime) /\
  felem_seq_as_nat s2 == toDomain_ ((y2D * z1D * z1D * z1D) % prime))


let move_from_jacobian_coordinates_lemma p q = 
  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 

  let x1 = Lib.Sequence.sub p 0 4 in 
  let y1 = Lib.Sequence.sub p 4 4 in 
  let z1 = Lib.Sequence.sub p 8 4 in 

  let x2 = Lib.Sequence.sub q 0 4 in 
  let y2 = Lib.Sequence.sub q 4 4 in 
  let z2 = Lib.Sequence.sub q 8 4 in 

  let x1D = fromDomain_ (felem_seq_as_nat x1) in 
  let y1D = fromDomain_ (felem_seq_as_nat y1) in 
  let z1D = fromDomain_ (felem_seq_as_nat z1) in 

  let x2D = fromDomain_ (felem_seq_as_nat x2) in 
  let y2D = fromDomain_ (felem_seq_as_nat y2) in 
  let z2D = fromDomain_ (felem_seq_as_nat z2) in 

  
  assert_by_tactic (x1D * (z2D * z2D) == x1D * z2D * z2D) canon;
  assert_by_tactic (x2D * (z1D * z1D) == x2D * z1D * z1D) canon;
  assert_by_tactic (y1D * (z2D * z2D * z2D) == y1D * z2D * z2D * z2D) canon;
  assert_by_tactic (y2D * (z1D * z1D * z1D) == y2D * z1D * z1D * z1D) canon;
  
   let z2Square = montgomery_multiplication_seq z2 z2 in 
   let z1Square = montgomery_multiplication_seq z1 z1 in 
   
   let z2Cube = montgomery_multiplication_seq z2Square z2 in 
     lemma_mod_mul_distr_l (z2D * z2D) z2D prime;
   let z1Cube = montgomery_multiplication_seq z1Square z1 in 
     lemma_mod_mul_distr_l (z1D * z1D) z1D prime;

   let u1 = montgomery_multiplication_seq x1 z2Square in
       lemma_mod_mul_distr_r x1D (z2D * z2D) prime;
   let u2 = montgomery_multiplication_seq x2 z1Square in 
       lemma_mod_mul_distr_r x2D (z1D * z1D) prime;

   let s1 = montgomery_multiplication_seq y1 z2Cube in 
       lemma_mod_mul_distr_r y1D (z2D * z2D * z2D) prime;
   let s2 = montgomery_multiplication_seq y2 z1Cube in 
       lemma_mod_mul_distr_r y2D (z1D * z1D * z1D) prime



noextract
val move_from_jacobian_coordinates_seq:  p: point_prime -> q: point_prime -> Tot (r: tuple4 felem_seq_prime felem_seq_prime felem_seq_prime felem_seq_prime {let u1, u2, s1, s2 = r in 
  let x1 = Lib.Sequence.sub p 0 4 in 
  let y1 = Lib.Sequence.sub p 4 4 in 
  let z1 = Lib.Sequence.sub p 8 4 in 

  let x2 = Lib.Sequence.sub q 0 4 in 
  let y2 = Lib.Sequence.sub q 4 4 in 
  let z2 = Lib.Sequence.sub q 8 4 in 

  let x1D = fromDomain_ (felem_seq_as_nat x1) in 
  let y1D = fromDomain_ (felem_seq_as_nat y1) in 
  let z1D = fromDomain_ (felem_seq_as_nat z1) in 

  let x2D = fromDomain_ (felem_seq_as_nat x2) in 
  let y2D = fromDomain_ (felem_seq_as_nat y2) in 
  let z2D = fromDomain_ (felem_seq_as_nat z2) in 

  felem_seq_as_nat u1 == toDomain_ ((x1D * z2D * z2D) % prime)  /\
  felem_seq_as_nat u2 == toDomain_ ((x2D * z1D * z1D) % prime) /\
  felem_seq_as_nat s1 == toDomain_ ((y1D * z2D * z2D * z2D) % prime) /\
  felem_seq_as_nat s2 == toDomain_ ((y2D * z1D * z1D * z1D) % prime)})



let move_from_jacobian_coordinates_seq p q = 
  let x1 = Lib.Sequence.sub p 0 4 in 
  let y1 = Lib.Sequence.sub p 4 4 in 
  let z1 = Lib.Sequence.sub p 8 4 in 

  let x2 = Lib.Sequence.sub q 0 4 in 
  let y2 = Lib.Sequence.sub q 4 4 in 
  let z2 = Lib.Sequence.sub q 8 4 in 

  let z2Square = montgomery_multiplication_seq z2 z2 in 
  let z1Square = montgomery_multiplication_seq z1 z1 in 
  let z2Cube = montgomery_multiplication_seq z2Square z2 in 
  let z1Cube = montgomery_multiplication_seq z1Square z1 in 

  let u1 = montgomery_multiplication_seq x1 z2Square in 
  let u2 = montgomery_multiplication_seq x2 z1Square in 

  let s1 = montgomery_multiplication_seq y1 z2Cube in 
  let s2 = montgomery_multiplication_seq y2 z1Cube in 
  
  move_from_jacobian_coordinates_lemma p q;
  (u1, u2, s1, s2)

  

val compute_common_params_point_add_seq: u1: felem_seq_prime -> u2: felem_seq_prime -> s1: felem_seq_prime -> s2: felem_seq_prime -> Tot (result: tuple4 felem_seq_prime felem_seq_prime felem_seq_prime felem_seq_prime{
  let h, r, uh, hCube = result in 
  let u1D = fromDomain_ (felem_seq_as_nat u1) in 
  let u2D = fromDomain_ (felem_seq_as_nat u2) in 
  let s1D = fromDomain_ (felem_seq_as_nat s1) in 
  let s2D = fromDomain_ (felem_seq_as_nat s2) in 
  let hD = fromDomain_ (felem_seq_as_nat h) in 

  felem_seq_as_nat h == toDomain_ ((u2D - u1D) % prime) /\
  felem_seq_as_nat r == toDomain_ ((s2D - s1D) % prime) /\
  felem_seq_as_nat uh == toDomain_ (u1D * hD * hD % prime) /\
  felem_seq_as_nat hCube == toDomain_ (hD * hD * hD % prime)
  
  })

let compute_common_params_point_add_seq u1 u2 s1 s2 = 
  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 

  let h = felem_sub_seq u2 u1 in 
  let r = felem_sub_seq s2 s1 in 
  let temp = montgomery_multiplication_seq h h in 
  let uh = montgomery_multiplication_seq u1 temp in 
    lemma_mod_mul_distr_r (fromDomain_ (felem_seq_as_nat u1)) ((fromDomain_ (felem_seq_as_nat h)) * (fromDomain_ (felem_seq_as_nat h))) prime;
    assert_by_tactic (let u1D = fromDomain_ (felem_seq_as_nat u1) in let hD = fromDomain_ (felem_seq_as_nat h) in 
      u1D * (hD * hD) == u1D * hD * hD) canon;

  let hCube = montgomery_multiplication_seq h temp in 
    lemma_mod_mul_distr_r (fromDomain_ (felem_seq_as_nat h)) (fromDomain_ (felem_seq_as_nat h) * fromDomain_ (felem_seq_as_nat h)) prime;
    assert_by_tactic (let hD = fromDomain_ (felem_seq_as_nat h) in hD * (hD * hD) == hD * hD * hD) canon;

  (h, r, uh, hCube)


noextract
val computeX3_point_add_seq: hCube: felem_seq_prime -> uh: felem_seq_prime -> r: felem_seq_prime -> Tot (x3: felem_seq_prime {
  let hCubeD = fromDomain_ (felem_seq_as_nat hCube) in 
  let uhD = fromDomain_ (felem_seq_as_nat uh) in 
  let rD = fromDomain_ (felem_seq_as_nat r) in 
  felem_seq_as_nat x3 < prime /\ 
  felem_seq_as_nat x3 = toDomain_ ((rD * rD - hCubeD - 2 * uhD) % prime)
  })
 
let computeX3_point_add_seq hCube uh r = 
  let rSquare = montgomery_multiplication_seq r r in 
  let r_h = felem_sub_seq rSquare hCube in  
  lemma_mod_add_distr (-fromDomain_ (felem_seq_as_nat hCube)) (fromDomain_ (felem_seq_as_nat r) * fromDomain_ (felem_seq_as_nat r)) prime;
  let twouh = mm_byTwo_seq uh in 
  let x3 = felem_sub_seq r_h twouh in 
    lemma_minus_distr (fromDomain_ (felem_seq_as_nat r) * fromDomain_ (felem_seq_as_nat r) - fromDomain_ (felem_seq_as_nat hCube)) (2 * fromDomain_ (felem_seq_as_nat uh));
  x3

noextract
val computeY3_point_add_seq: s1: felem_seq_prime -> hCube: felem_seq_prime -> uh: felem_seq_prime -> x3_out: felem_seq_prime -> r: felem_seq_prime -> Tot (y3: felem_seq_prime {
  let s1D = fromDomain_ (felem_seq_as_nat s1) in 
  let hCubeD = fromDomain_ (felem_seq_as_nat hCube) in 
  let uhD = fromDomain_ (felem_seq_as_nat uh) in 
  let x3D = fromDomain_ (felem_seq_as_nat x3_out) in 
  let rD = fromDomain_ (felem_seq_as_nat r) in
  felem_seq_as_nat y3 < prime /\ 
  felem_seq_as_nat y3 = toDomain_ ((rD * (uhD - x3D) - s1D * hCubeD) % prime)
  })

let computeY3_point_add_seq s1 hCube uh x3_out r = 
  let s1hCube = montgomery_multiplication_seq s1 hCube in 
  let u1hx3 = felem_sub_seq uh x3_out in 
  let ru1hx3 = montgomery_multiplication_seq r u1hx3 in 
  let y3 = felem_sub_seq ru1hx3 s1hCube in 

  let s1D = fromDomain_ (felem_seq_as_nat s1) in 
  let hCubeD = fromDomain_ (felem_seq_as_nat hCube) in 
  let uhD = fromDomain_ (felem_seq_as_nat uh) in 
  let x3D = fromDomain_ (felem_seq_as_nat x3_out) in 
  let rD = fromDomain_ (felem_seq_as_nat r) in

  assert(felem_seq_as_nat s1hCube = toDomain_ (s1D * hCubeD % prime));
  assert(felem_seq_as_nat u1hx3 = toDomain_ ((uhD - x3D) % prime));
  assert(felem_seq_as_nat ru1hx3 = toDomain_(rD * ((uhD - x3D) % prime) % prime));
  lemma_mod_mul_distr_r rD (uhD -x3D) prime;
  lemma_minus_distr (rD * (uhD - x3D)) (s1D * hCubeD);

  y3 

noextract
val computeZ3_point_add_seq: z1: felem_seq_prime -> z2: felem_seq_prime -> h: felem_seq_prime -> 
  Tot (z3: felem_seq_prime {
    let z1D = fromDomain_ (felem_seq_as_nat z1) in 
    let z2D = fromDomain_ (felem_seq_as_nat z2) in 
    let hD = fromDomain_ (felem_seq_as_nat h) in 
    felem_seq_as_nat z3 < prime /\
    felem_seq_as_nat z3 = toDomain_ (hD * z1D * z2D % prime)
    })

let computeZ3_point_add_seq z1 z2 h = 
  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 


  let z1z2 = montgomery_multiplication_seq z1 z2 in 
  let z3 = montgomery_multiplication_seq h z1z2 in 

  let z1D = fromDomain_ (felem_seq_as_nat z1) in 
  let z2D = fromDomain_ (felem_seq_as_nat z2) in 
  let hD = fromDomain_ (felem_seq_as_nat h) in 
  
  lemma_mod_mul_distr_r hD (z1D * z2D) prime;
  assert_by_tactic (hD * (z1D * z2D) = hD * z1D * z2D) canon;
  z3

noextract
val compare_felem_seq: a: felem_seq_prime -> b: felem_seq_prime -> Tot (r: uint64 {if felem_seq_as_nat a = felem_seq_as_nat b then uint_v r == pow2 64 - 1 else uint_v r = 0})

let compare_felem_seq a b = 
  let a_0 = Lib.Sequence.index a 0 in 
  let a_1 = Lib.Sequence.index a 1 in 
  let a_2 = Lib.Sequence.index a 2 in 
  let a_3 = Lib.Sequence.index a 3 in 

  let b_0 = Lib.Sequence.index b 0 in 
  let b_1 = Lib.Sequence.index b 1 in 
  let b_2 = Lib.Sequence.index b 2 in 
  let b_3 = Lib.Sequence.index b 3 in 

  let r = equalFelem (a_0, a_1, a_2, a_3) (b_0, b_1, b_2, b_3) in 
  r

noextract
val isZero_seq: f: felem_seq_prime -> Tot (r: uint64 {if felem_seq_as_nat f = 0 then uint_v r== pow2 64 - 1 else uint_v r == 0})

let isZero_seq f = 
  let a0 = Lib.Sequence.index f 0 in 
  let a1 = Lib.Sequence.index f 1 in 
  let a2 = Lib.Sequence.index f 2 in 
  let a3 = Lib.Sequence.index f 3 in 
  isZero_tuple_u (a0, a1, a2, a3)

noextract
val point_double_condition_seq: u1: felem_seq_prime -> u2: felem_seq_prime -> s1: felem_seq_prime -> s2: felem_seq_prime -> z1: felem_seq_prime -> z2: felem_seq_prime -> Tot (r: bool {
  let u1D = fromDomain_ (felem_seq_as_nat u1) in 
  let u2D = fromDomain_ (felem_seq_as_nat u2) in 
  let s1D = fromDomain_ (felem_seq_as_nat s1) in 
  let s2D = fromDomain_ (felem_seq_as_nat s2) in 
  let z1D = fromDomain_ (felem_seq_as_nat z1) in 
  let z2D = fromDomain_ (felem_seq_as_nat z2) in 
  if u1D = u2D && s1D = s2D && z1D <> 0 && z2D <> 0 then r == true else r == false})


let point_double_condition_seq u1 u2 s1 s2 z1 z2 = 
  let one = compare_felem_seq u1 u2 in 
  let two = compare_felem_seq s1 s2 in 
  let z1NotZero = isZero_seq z1 in 
  let z2NotZero = isZero_seq z2 in 
  let pointsInfinity = logand (lognot z1NotZero) (lognot z2NotZero) in 
    lognot_lemma z1NotZero;
    lognot_lemma z2NotZero;
    logand_lemma (lognot z1NotZero) (lognot z2NotZero);
    lemma_log_and1 (lognot z1NotZero) (lognot z2NotZero);  
  let onetwo = logand one two in 
    logand_lemma one two;
    lemma_log_and1 one two;
  let result = logand onetwo pointsInfinity in 
    lemma_log_and1 onetwo pointsInfinity;
    lemmaFromDomain (felem_seq_as_nat u1);
    lemmaFromDomain (felem_seq_as_nat u2);
    lemmaFromDomain (felem_seq_as_nat s1);
    lemmaFromDomain (felem_seq_as_nat s2);
    
    lemma_modular_multiplication_p256 (felem_seq_as_nat u1) (felem_seq_as_nat u2); 
    lemma_modular_multiplication_p256 (felem_seq_as_nat s1) (felem_seq_as_nat s2); 

    assert_norm (modp_inv2 (pow2 256) > 0);
    assert_norm (modp_inv2 (pow2 256) % prime <> 0); 

    lemma_multiplication_not_mod_prime (felem_seq_as_nat z1) (modp_inv2 (pow2 256));
    lemma_multiplication_not_mod_prime (felem_seq_as_nat z2) (modp_inv2 (pow2 256));
    lemmaFromDomain (felem_seq_as_nat z1);
    lemmaFromDomain (felem_seq_as_nat z2);
    eq_u64 result (u64 (u64 0xffffffffffffffff))     

val copy_conditional_tuple: out: felem4{as_nat4 out < prime} -> x: felem4 {as_nat4 x < prime} -> 
  mask: uint64 {uint_v mask = 0 \/ uint_v mask = pow2 64 - 1} -> 
  Tot (result: felem4 {as_nat4 result < prime /\ (
  let (out_0, out_1, out_2, out_3) = out in 
  let (x_0, x_1, x_2, x_3) = x in
  let (r_0, r_1, r_2, r_3) = result in 
  if uint_v mask = pow2 64 - 1 then (as_nat4 result == as_nat4 x /\ r_0 == x_0 /\ r_1 == x_1 /\ r_2 == x_2 /\ r_3 == x_3) else
  as_nat4 result == as_nat4 out /\ r_0 == out_0 /\ r_1 == out_1 /\ r_2 == out_2 /\ r_3 == out_3)})

let copy_conditional_tuple out x mask = 
  let (out_0, out_1, out_2, out_3) = out in 
  let (x_0, x_1, x_2, x_3) = x in 

  let r_0 = logxor out_0 (logand mask (logxor out_0 x_0)) in 
  let r_1 = logxor out_1 (logand mask (logxor out_1 x_1)) in 
  let r_2 = logxor out_2 (logand mask (logxor out_2 x_2)) in 
  let r_3 = logxor out_3 (logand mask (logxor out_3 x_3)) in 
    
  lemma_xor_copy_cond out_0 x_0 mask;
  lemma_xor_copy_cond out_1 x_1 mask;
  lemma_xor_copy_cond out_2 x_2 mask;
  lemma_xor_copy_cond out_3 x_3 mask;
  (r_0, r_1, r_2, r_3)

noextract
val copy_conditional_seq: out: felem_seq_prime -> x: felem_seq_prime  -> mask: uint64{uint_v mask = 0 \/ uint_v mask = pow2 64 - 1} -> 
  Tot (result: felem_seq_prime {if uint_v mask = pow2 64 - 1 then Lib.Sequence.equal result x else Lib.Sequence.equal result out})

let copy_conditional_seq out x mask = 
  let out_0 = index out 0 in 
  let out_1 = index out 1 in 
  let out_2 = index out 2 in 
  let out_3 = index out 3 in 

  let x_0 = index x 0 in 
  let x_1 = index x 1 in 
  let x_2 = index x 2 in 
  let x_3 = index x 3 in 

  let (r_0, r_1, r_2, r_3)  = copy_conditional_tuple (out_0, out_1, out_2, out_3) (x_0, x_1, x_2, x_3) mask in 

  let result = Lib.Sequence.create 4 (u64 0) in 
  let result = Lib.Sequence.upd result 0 r_0 in 
  let result = Lib.Sequence.upd result 1 r_1 in 
  let result = Lib.Sequence.upd result 2 r_2 in 
  let result = Lib.Sequence.upd result 3 r_3 in 

  assert(if uint_v mask = pow2 64 - 1 then Lib.Sequence.equal result x else Lib.Sequence.equal result out);

  result


noextract
val copy_point_conditional_seq: x3 : felem_seq_prime -> y3: felem_seq_prime -> z3: felem_seq_prime -> p: point_prime -> maskPoint: point_prime -> Tot (result: tuple3 felem_seq_prime felem_seq_prime felem_seq_prime {
  let p_x = Lib.Sequence.sub p 0 4 in 
  let p_y = Lib.Sequence.sub p 4 4 in 
  let p_z = Lib.Sequence.sub p 8 4 in 

  let (x3_out, y3_out, z3_out) = result in 
  let z = Lib.Sequence.sub maskPoint 8 4 in 
  if felem_seq_as_nat z = 0 then 
    x3_out == p_x /\ y3_out == p_y /\ z3_out == p_z 
  else
    x3_out == x3 /\ y3_out == y3 /\ z3_out == z3 
  })
 

let copy_point_conditional_seq x3 y3 z3 p maskPoint = 
   let z = Lib.Sequence.sub maskPoint 8 4 in  
   let mask = isZero_seq z in 
   let p_x = Lib.Sequence.sub p 0 4 in 
   let p_y = Lib.Sequence.sub p 4 4 in 
   let p_z = Lib.Sequence.sub p 8 4 in 
   
   let x3_out = copy_conditional_seq x3 p_x mask in 
   let y3_out = copy_conditional_seq y3 p_y mask in 
   let z3_out = copy_conditional_seq z3 p_z mask in 
   (x3_out, y3_out, z3_out)


#reset-options "--z3rlimit 100"  
noextract
val point_add_if_second_branch_seq: 
  p: point_prime -> q: point_prime ->  
  u1: felem_seq_prime -> u2: felem_seq_prime -> s1: felem_seq_prime -> s2: felem_seq_prime
    {let u1_, u2_, s1_, s2_ = move_from_jacobian_coordinates_seq p q in 
    u1 == u1_ /\ u2_ == u2 /\ s1_ == s1 /\ s2_ == s2} ->
  r: felem_seq_prime -> h: felem_seq_prime -> uh: felem_seq_prime -> hCube: felem_seq_prime
  {let h_, r_,  uh_, hCube_ = compute_common_params_point_add_seq u1 u2 s1 s2 in 
    h_ == h /\ r_ == r /\ uh_ == uh /\ hCube_ == hCube}
  
  ->
  Tot (result: point_prime {
    let x1 = Lib.Sequence.sub p 0 4 in 
    let y1 = Lib.Sequence.sub p 4 4 in 
    let z1 = Lib.Sequence.sub p 8 4 in 

    let x2 = Lib.Sequence.sub q 0 4 in 
    let y2 = Lib.Sequence.sub q 4 4 in 
    let z2 = Lib.Sequence.sub q 8 4 in 


    let x3 = Lib.Sequence.sub result 0 4 in
    let y3 = Lib.Sequence.sub result 4 4 in 
    let z3 = Lib.Sequence.sub result 8 4 in 
 
  let rD = fromDomain_ (felem_seq_as_nat r) in 
  let hD = fromDomain_ (felem_seq_as_nat h) in 
  let s1D = fromDomain_ (felem_seq_as_nat s1) in 
  let u1D = fromDomain_ (felem_seq_as_nat u1) in 

  let x1D = fromDomain_ (felem_seq_as_nat x1) in 
  let x2D = fromDomain_ (felem_seq_as_nat x2) in 

  let y1D = fromDomain_ (felem_seq_as_nat y1) in 
  let y2D = fromDomain_ (felem_seq_as_nat y2) in 

  let z1D = fromDomain_ (felem_seq_as_nat z1) in 
  let z2D = fromDomain_ (felem_seq_as_nat z2) in 

  let x3D = fromDomain_ (felem_seq_as_nat x3) in 

  if z2D = 0 then felem_seq_as_nat x3 == toDomain_(x1D) /\ felem_seq_as_nat y3 == toDomain_(y1D) /\ felem_seq_as_nat z3 == toDomain_(z1D) 
       else if z1D = 0 then felem_seq_as_nat x3 == toDomain_(x2D)  /\ felem_seq_as_nat y3 == toDomain_(y2D)  /\ felem_seq_as_nat z3 == toDomain_(z2D) 
       else felem_seq_as_nat x3 == toDomain_ ((rD * rD - hD * hD * hD - 2 * u1D * hD * hD) % prime) /\ felem_seq_as_nat y3 == toDomain_((rD * (u1D * hD * hD - x3D) - s1D * hD*hD*hD) % prime) /\ felem_seq_as_nat z3 == toDomain_ (hD * z1D * z2D % prime)
  
  })

noextract
val lemma_move_x: 
  u1: felem_seq_prime -> u2: felem_seq_prime -> s1: felem_seq_prime -> s2: felem_seq_prime  -> 
  r: felem_seq_prime -> h: felem_seq_prime -> uh: felem_seq_prime -> hCube: felem_seq_prime
  {let h_, r_,  uh_, hCube_ = compute_common_params_point_add_seq u1 u2 s1 s2 in 
    h_ == h /\ r_ == r /\ uh_ == uh /\ hCube_ == hCube} ->
x3: felem_seq_prime {
  let rD = fromDomain_ (felem_seq_as_nat r) in 
  let hCubeD = fromDomain_ (felem_seq_as_nat hCube) in 
  let uhD = fromDomain_ (felem_seq_as_nat uh) in 

felem_seq_as_nat x3 = toDomain_ ((rD * rD - hCubeD - 2 * uhD) % prime)} -> Lemma (
  let rD = fromDomain_ (felem_seq_as_nat r) in 
  let hD = fromDomain_ (felem_seq_as_nat h) in 
  let hCubeD = fromDomain_ (felem_seq_as_nat hCube) in 
  let uhD = fromDomain_ (felem_seq_as_nat uh) in 
  let u1D = fromDomain_ (felem_seq_as_nat u1) in 

felem_seq_as_nat x3 == toDomain_ ((rD * rD - hD * hD * hD - 2 * u1D * hD * hD) % prime))

let lemma_move_x u1 u2 s1 s2 r h uh hCube x3 = 
  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 

  let rD = fromDomain_ (felem_seq_as_nat r) in 
  let hD = fromDomain_ (felem_seq_as_nat h) in 
  let hCubeD = fromDomain_ (felem_seq_as_nat hCube) in 
  let uhD = fromDomain_ (felem_seq_as_nat uh) in 
  let u1D = fromDomain_ (felem_seq_as_nat u1) in 

  let k = 2 * (u1D * hD * hD % prime) in 
  lemma_mod_sub_distr (rD * rD - hCubeD) k prime;
  lemma_mod_mul_distr_r 2 (u1D * hD * hD) prime; 
  assert_by_tactic (2 * (u1D * hD * hD)  = 2 * u1D * hD * hD) canon;
  lemma_mod_sub_distr (rD * rD - (hD * hD * hD % prime)) (2 * u1D * hD * hD) prime;
  lemma_mod_sub_distr (rD * rD - 2 * u1D * hD * hD) (hD * hD * hD) prime
  
noextract
val lemma_move_y: 
  u1: felem_seq_prime -> u2: felem_seq_prime -> s1: felem_seq_prime -> s2: felem_seq_prime  -> 
  r: felem_seq_prime -> h: felem_seq_prime -> uh: felem_seq_prime -> hCube: felem_seq_prime
    {let h_, r_,  uh_, hCube_ = compute_common_params_point_add_seq u1 u2 s1 s2 in h_ == h /\ r_ == r /\ uh_ == uh /\ hCube_ == hCube} ->
  x3D: nat ->
  y3: felem_seq_prime {
    let rD = fromDomain_ (felem_seq_as_nat r) in 
    let hCubeD = fromDomain_ (felem_seq_as_nat hCube) in 
    let uhD = fromDomain_ (felem_seq_as_nat uh) in 
    let s1D = fromDomain_ (felem_seq_as_nat s1) in 
    felem_seq_as_nat y3 = toDomain_ ((rD * (uhD - x3D) - s1D * hCubeD) % prime)} -> 
  Lemma (
    let rD = fromDomain_ (felem_seq_as_nat r) in 
    let hCubeD = fromDomain_ (felem_seq_as_nat hCube) in 
    let uhD = fromDomain_ (felem_seq_as_nat uh) in 
    let s1D = fromDomain_ (felem_seq_as_nat s1) in 
    let u1D = fromDomain_ (felem_seq_as_nat u1) in 
    let hD = fromDomain_ (felem_seq_as_nat h) in 
    felem_seq_as_nat y3 == toDomain_((rD * (u1D * hD * hD - x3D) - s1D * hD*hD*hD) % prime))

let lemma_move_y u1 u2 s1 s2 r h uh hCube x3D y3 = 
    let open FStar.Tactics in 
    let open FStar.Tactics.Canon in 

    let rD = fromDomain_ (felem_seq_as_nat r) in 
    let hCubeD = fromDomain_ (felem_seq_as_nat hCube) in 
    let uhD = fromDomain_ (felem_seq_as_nat uh) in 
    let s1D = fromDomain_ (felem_seq_as_nat s1) in 
    let u1D = fromDomain_ (felem_seq_as_nat u1) in 
    let hD = fromDomain_ (felem_seq_as_nat h) in 
    let r0 = u1D * hD * hD in 
    let r1 = hD * hD * hD in 
    lemma_mod_sub_distr (rD * (r0 % prime - x3D)) (s1D * (r1 % prime)) prime;
    lemma_mod_mul_distr_r s1D r1 prime;
    lemma_mod_sub_distr (rD * (r0 % prime - x3D)) (s1D * r1) prime;
    lemma_mod_add_distr (-(s1D * r1)) (rD * (r0 % prime - x3D)) prime;
    lemma_mod_mul_distr_r rD (r0 % prime - x3D) prime;
    lemma_mod_add_distr (-x3D) r0 prime;
    lemma_mod_mul_distr_r rD (r0 - x3D) prime;
    lemma_mod_add_distr (- (s1D * r1)) (rD * (r0 - x3D)) prime;
    assert_by_tactic (s1D * (hD * hD * hD) == s1D * hD * hD * hD) canon


val lemma_test: x1: felem_seq_prime -> y1: felem_seq_prime -> z1: felem_seq_prime -> 
  x2: felem_seq_prime -> y2: felem_seq_prime -> z2: felem_seq_prime -> 
  x3_out : felem_seq_prime -> y3_out: felem_seq_prime -> z3_out: felem_seq_prime -> 
  x3: felem_seq_prime -> y3: felem_seq_prime -> z3: felem_seq_prime -> 
  Lemma 
  (requires (
    let z1D = fromDomain_ (felem_seq_as_nat z1) in 
    let z2D = fromDomain_ (felem_seq_as_nat z2) in 
    if z2D = 0 then x3_out == x1 /\ y3_out == y1  /\ z3_out == z1 
       else if z1D = 0 then x3_out == x2 /\ y3_out == y2 /\ z3_out == z2
       else x3_out == x3 /\ y3_out == y3 /\ z3_out == z3))

(ensures (
    let z1D = fromDomain_ (felem_seq_as_nat z1) in 
    let z2D = fromDomain_ (felem_seq_as_nat z2) in 
    if z2D = 0 then 
      felem_seq_as_nat x3_out == toDomain_(fromDomain_ (felem_seq_as_nat x1)) /\ 
      felem_seq_as_nat y3_out == toDomain_(fromDomain_ (felem_seq_as_nat y1)) /\ 
      felem_seq_as_nat z3_out == toDomain_(fromDomain_ (felem_seq_as_nat z1))
    else if z1D = 0 then 
      felem_seq_as_nat x3_out ==  toDomain_(fromDomain_ (felem_seq_as_nat x2)) /\ 
      felem_seq_as_nat y3_out ==  toDomain_(fromDomain_ (felem_seq_as_nat y2))  /\ 
      felem_seq_as_nat z3_out ==  toDomain_(fromDomain_ (felem_seq_as_nat z2))
    else 
      x3_out == x3 /\ y3_out == y3 /\ z3_out == z3))   


let lemma_test x1 y1 z1 x2 y2 z2 x3_out y3_out z3_out x3 y3 z3 = 
  lemmaFromDomainToDomain (felem_seq_as_nat x1);
  lemmaFromDomainToDomain (felem_seq_as_nat y1);
  lemmaFromDomainToDomain (felem_seq_as_nat z1);
  lemmaFromDomainToDomain (felem_seq_as_nat x2);
  lemmaFromDomainToDomain (felem_seq_as_nat y2);
  lemmaFromDomainToDomain (felem_seq_as_nat z2)

#reset-options "--z3rlimit 300"  

let point_add_if_second_branch_seq p q u1 u2 s1 s2 r h uh hCube = 
    let x1 = Lib.Sequence.sub p 0 4 in 
    let y1 = Lib.Sequence.sub p 4 4 in 
    let z1 = Lib.Sequence.sub p 8 4 in 

    let x2 = Lib.Sequence.sub q 0 4 in 
    let y2 = Lib.Sequence.sub q 4 4 in 
    let z2 = Lib.Sequence.sub q 8 4 in

  let x3 = computeX3_point_add_seq hCube uh r in 
    lemma_move_x u1 u2 s1 s2 r h uh hCube x3; 
    let x3D = fromDomain_ (felem_seq_as_nat x3) in 
  let y3 = computeY3_point_add_seq s1 hCube uh x3 r in 
    lemma_move_y u1 u2 s1 s2 r h uh hCube x3D y3; 
  let z3 = computeZ3_point_add_seq z1 z2 h in  
  let (x3_out, y3_out, z3_out) = copy_point_conditional_seq x3 y3 z3 q p in 

  let (x3_out1, y3_out1, z3_out1) = copy_point_conditional_seq x3_out y3_out z3_out p q in 

  let r = concat (concat x3_out1 y3_out1) z3_out1 in 

  assert_norm (modp_inv2 (pow2 256) > 0);
  assert_norm (modp_inv2 (pow2 256) % prime <> 0); 

  lemma_multiplication_not_mod_prime (felem_seq_as_nat z1) (modp_inv2 (pow2 256));
  lemma_multiplication_not_mod_prime (felem_seq_as_nat z2) (modp_inv2 (pow2 256));
  lemmaFromDomain (felem_seq_as_nat z1);
  lemmaFromDomain (felem_seq_as_nat z2);

   lemma_test x1 y1 z1 x2 y2 z2 x3_out1 y3_out1 z3_out1 x3 y3 z3; 
  r

 
val lemma_xToSpecification : x1D: nat -> y1D: nat -> z1D: nat -> x2D: nat -> y2D: nat -> z2D: nat -> 
  u1: felem_seq_prime{felem_seq_as_nat u1 = toDomain_ (x1D * z2D * z2D % prime)} -> 
  u2: felem_seq_prime{felem_seq_as_nat u2 = toDomain_ (x2D * z1D * z1D % prime)} -> 
  s1: felem_seq_prime{felem_seq_as_nat s1 = toDomain_ (y1D * z2D * z2D * z2D % prime)} -> 
  s2: felem_seq_prime{felem_seq_as_nat s2 = toDomain_ (y2D * z1D * z1D * z1D % prime)} -> 
  x3: felem_seq_prime{ 
    let u1D = fromDomain_ (felem_seq_as_nat u1) in let u2D = fromDomain_ (felem_seq_as_nat u2) in 
    let s1D = fromDomain_ (felem_seq_as_nat s1) in let s2D = fromDomain_ (felem_seq_as_nat s2) in  
      if u1D = u2D && s1D = s2D && z1D <> 0 && z2D <> 0 then 
	let (xN, yN, zN) = _point_double (x1D, y1D, z1D) in fromDomain_ (felem_seq_as_nat x3) == xN 
      else True} -> 
   y3: felem_seq_prime{
    let u1D = fromDomain_ (felem_seq_as_nat u1) in let u2D = fromDomain_ (felem_seq_as_nat u2) in 
    let s1D = fromDomain_ (felem_seq_as_nat s1) in let s2D = fromDomain_ (felem_seq_as_nat s2) in  
      if u1D = u2D && s1D = s2D && z1D <> 0 && z2D <> 0 then 
	let (xN, yN, zN) = _point_double (x1D, y1D, z1D) in fromDomain_ (felem_seq_as_nat y3) == yN 
      else True} ->
   z3: felem_seq_prime{
    let u1D = fromDomain_ (felem_seq_as_nat u1) in let u2D = fromDomain_ (felem_seq_as_nat u2) in 
    let s1D = fromDomain_ (felem_seq_as_nat s1) in let s2D = fromDomain_ (felem_seq_as_nat s2) in  
      if u1D = u2D && s1D = s2D && z1D <> 0 && z2D <> 0 then 
	let (xN, yN, zN) = _point_double (x1D, y1D, z1D) in fromDomain_ (felem_seq_as_nat z3) == zN 
      else True}
  ->  
  Lemma (    
    let (xN, yN, zN) = _point_add (x1D, y1D, z1D) (x2D, y2D, z2D) in
    let u1D = fromDomain_ (felem_seq_as_nat u1) in let u2D = fromDomain_ (felem_seq_as_nat u2) in 
    let s1D = fromDomain_ (felem_seq_as_nat s1) in let s2D = fromDomain_ (felem_seq_as_nat s2) in 
    if u1D = u2D && s1D = s2D && z1D <> 0 && z2D <> 0 
      then toDomain_ xN == felem_seq_as_nat x3 /\ toDomain_ yN == felem_seq_as_nat y3 /\ toDomain_ zN == felem_seq_as_nat z3  else True)

let lemma_xToSpecification x1D y1D z1D x2D y2D z2D u1 u2 s1 s2  x3 y3 z3 = 
    let open FStar.Tactics in 
    let open FStar.Tactics.Canon in 
    let u1D = fromDomain_ (felem_seq_as_nat u1) in let u2D = fromDomain_ (felem_seq_as_nat u2) in 
    let s1D = fromDomain_ (felem_seq_as_nat s1) in let s2D = fromDomain_ (felem_seq_as_nat s2) in  
    
    let (xN, yN, zN) = _point_add (x1D, y1D, z1D) (x2D, y2D, z2D) in 
    let (xDouble, yDouble, zDouble) = _point_double (x1D, y1D, z1D) in 
    
    let u1N = x1D * z2D * z2D % prime in 
    let u2N = x2D * z1D * z1D % prime in 
    let s1N = y1D * z2D * z2D * z2D % prime in 
    let s2N = y2D * z1D * z1D * z1D % prime in 

    assert_by_tactic (x1D * z2D * z2D = x1D * (z2D * z2D)) canon;
    assert_by_tactic (x2D * z1D * z1D = x2D * (z1D * z1D)) canon;
    
    assert_by_tactic (y1D * z2D * (z2D * z2D) = y1D * z2D * z2D * z2D) canon;
    assert_by_tactic (y2D * z1D * (z1D * z1D) = y2D * z1D * z1D * z1D) canon;

     lemmaToDomainAndBackIsTheSame (u1N);
     lemmaToDomainAndBackIsTheSame (u2N);
     lemmaToDomainAndBackIsTheSame (s1N);
     lemmaToDomainAndBackIsTheSame (s2N);
     
     lemmaFromDomainToDomain (felem_seq_as_nat x3);
     lemmaFromDomainToDomain (felem_seq_as_nat y3);
     lemmaFromDomainToDomain (felem_seq_as_nat z3)
       
noextract       
val lemma_xToSpecification_after_double : x1D: nat -> y1D: nat -> z1D: nat -> x2D: nat -> y2D: nat -> z2D: nat -> 
  u1: felem_seq_prime{felem_seq_as_nat u1 = toDomain_ (x1D * z2D * z2D % prime)} -> 
  u2: felem_seq_prime{felem_seq_as_nat u2 = toDomain_ (x2D * z1D * z1D % prime)} -> 
  s1: felem_seq_prime{felem_seq_as_nat s1 = toDomain_ (y1D * z2D * z2D * z2D % prime)} -> 
  s2: felem_seq_prime{felem_seq_as_nat s2 = toDomain_ (y2D * z1D * z1D * z1D % prime)} -> 
  h: felem_seq_prime {
    let u1D = fromDomain_ (felem_seq_as_nat u1) in let u2D = fromDomain_ (felem_seq_as_nat u2) in 
    let s1D = fromDomain_ (felem_seq_as_nat s1) in let s2D = fromDomain_ (felem_seq_as_nat s2) in  
    felem_seq_as_nat h = toDomain_ ((u2D - u1D) % prime)} ->
  r: felem_seq_prime {
    let u1D = fromDomain_ (felem_seq_as_nat u1) in let u2D = fromDomain_ (felem_seq_as_nat u2) in 
    let s1D = fromDomain_ (felem_seq_as_nat s1) in let s2D = fromDomain_ (felem_seq_as_nat s2) in  
    felem_seq_as_nat r = toDomain_ ((s2D - s1D) % prime)} -> 
  x3: felem_seq_prime{
    let u1D = fromDomain_ (felem_seq_as_nat u1) in let u2D = fromDomain_ (felem_seq_as_nat u2) in 
    let s1D = fromDomain_ (felem_seq_as_nat s1) in let s2D = fromDomain_ (felem_seq_as_nat s2) in  
    let hD = fromDomain_ (felem_seq_as_nat h) in let rD = fromDomain_ (felem_seq_as_nat r) in 
      if not(u1D = u2D && s1D = s2D && z1D <> 0 && z2D <> 0) then
	begin 
	  if z2D = 0 then felem_seq_as_nat x3 == toDomain_ (x1D)
	  else if z1D = 0 then felem_seq_as_nat x3 == toDomain_ (x2D) 
	  else	felem_seq_as_nat x3 == toDomain_ ((rD * rD - hD * hD * hD - 2 * u1D * hD * hD) % prime)
	end  
      else True
      } ->  
  y3: felem_seq_prime {
    let u1D = fromDomain_ (felem_seq_as_nat u1) in let u2D = fromDomain_ (felem_seq_as_nat u2) in 
    let s1D = fromDomain_ (felem_seq_as_nat s1) in let s2D = fromDomain_ (felem_seq_as_nat s2) in  
    let hD = fromDomain_ (felem_seq_as_nat h) in let rD = fromDomain_ (felem_seq_as_nat r) in 
    let x3D = fromDomain_ (felem_seq_as_nat x3) in 
    
      if not(u1D = u2D && s1D = s2D && z1D <> 0 && z2D <> 0) then
	begin 
	  if z2D = 0 then felem_seq_as_nat y3 == toDomain_ (y1D)
	  else if z1D = 0 then felem_seq_as_nat y3 == toDomain_ (y2D) 
	  else	felem_seq_as_nat y3 == toDomain_ ((rD * (u1D * hD * hD - x3D) - s1D * hD*hD*hD) % prime)
	end  
      else True
      } ->
   z3 : felem_seq_prime {
    let u1D = fromDomain_ (felem_seq_as_nat u1) in let u2D = fromDomain_ (felem_seq_as_nat u2) in 
    let s1D = fromDomain_ (felem_seq_as_nat s1) in let s2D = fromDomain_ (felem_seq_as_nat s2) in  
    let hD = fromDomain_ (felem_seq_as_nat h) in 

      if not(u1D = u2D && s1D = s2D && z1D <> 0 && z2D <> 0) then
	begin  
	  if z2D = 0 then felem_seq_as_nat z3 == toDomain_ (z1D)
	  else if z1D = 0 then felem_seq_as_nat z3 == toDomain_ (z2D) 
	  else	felem_seq_as_nat z3 == toDomain_ ((hD * z1D * z2D) % prime)
	end  
      else True
      }
   -> 

  Lemma (    
    let (xN, yN, zN) = _point_add (x1D, y1D, z1D) (x2D, y2D, z2D) in
    let u1D = fromDomain_ (felem_seq_as_nat u1) in let u2D = fromDomain_ (felem_seq_as_nat u2) in 
    let s1D = fromDomain_ (felem_seq_as_nat s1) in let s2D = fromDomain_ (felem_seq_as_nat s2) in 
    if not(u1D = u2D && s1D = s2D && z1D <> 0 && z2D <> 0)
      then toDomain_ xN == felem_seq_as_nat x3 /\ toDomain_ yN == felem_seq_as_nat y3 /\ toDomain_ zN == felem_seq_as_nat z3 else True)


let lemma_xToSpecification_after_double x1D y1D z1D x2D y2D z2D u1 u2 s1 s2 h r x3 y3 z3 = 
    let open FStar.Tactics in 
    let open FStar.Tactics.Canon in 
    let s1D = fromDomain_ (felem_seq_as_nat s1) in
    
    let hD = fromDomain_ (felem_seq_as_nat h) in let rD = fromDomain_ (felem_seq_as_nat r) in 
    
    let (xN, yN, zN) = _point_add (x1D, y1D, z1D) (x2D, y2D, z2D) in 

    let u1N = x1D * z2D * z2D % prime in 
    let u2N = x2D * z1D * z1D % prime in 
    let s1N = y1D * z2D * z2D * z2D % prime in 
    let s2N = y2D * z1D * z1D * z1D % prime in 

    let hN = (u2N - u1N) % prime in 
    let rN = (s2N - s1N) % prime in 

    assert_by_tactic (x1D * z2D * z2D = x1D * (z2D * z2D)) canon;
    assert_by_tactic (x2D * z1D * z1D = x2D * (z1D * z1D)) canon;
    
    assert_by_tactic (y1D * z2D * (z2D * z2D) = y1D * z2D * z2D * z2D) canon;
    assert_by_tactic (y2D * z1D * (z1D * z1D) = y2D * z1D * z1D * z1D) canon;

    assert_by_tactic (forall (n: nat). n * hN * hN = n * (hN * hN)) canon; 
    assert_by_tactic (s1D * (hD * hD * hD) = s1D * hD * hD * hD) canon;

     lemmaToDomainAndBackIsTheSame (u1N);
     lemmaToDomainAndBackIsTheSame (u2N);
     lemmaToDomainAndBackIsTheSame (s1N);
     lemmaToDomainAndBackIsTheSame (s2N);
 
     lemmaToDomainAndBackIsTheSame (hN);
     lemmaToDomainAndBackIsTheSame (rN);

     lemmaFromDomainToDomain (felem_seq_as_nat x3);
     lemmaFromDomainToDomain (felem_seq_as_nat y3);
     lemmaFromDomainToDomain (felem_seq_as_nat z3)


#reset-options "--z3rlimit 500" 
noextract
val point_add_seq: p: point_prime -> q: point_prime -> Tot (r: point_prime {
   let x3:felem_seq_prime   = Lib.Sequence.sub r 0 4 in
   let y3:felem_seq_prime   = Lib.Sequence.sub r 4 4 in
   let z3:felem_seq_prime   = Lib.Sequence.sub r 8 4 in

    let x1:felem_seq_prime  = Lib.Sequence.sub p 0 4 in 
    let y1:felem_seq_prime  = Lib.Sequence.sub p 4 4 in 
    let z1:felem_seq_prime  = Lib.Sequence.sub p 8 4 in 

    let x2:felem_seq_prime  = Lib.Sequence.sub q 0 4 in 
    let y2:felem_seq_prime  = Lib.Sequence.sub q 4 4 in 
    let z2:felem_seq_prime  = Lib.Sequence.sub q 8 4 in 

   let pxD = fromDomain_ (felem_seq_as_nat x1) in 
   let pyD = fromDomain_ (felem_seq_as_nat y1) in 
   let pzD = fromDomain_ (felem_seq_as_nat z1) in 

   let qxD = fromDomain_ (felem_seq_as_nat x2) in 
   let qyD = fromDomain_ (felem_seq_as_nat y2) in 
   let qzD = fromDomain_ (felem_seq_as_nat z2) in 
   
   let (xN, yN, zN) = _point_add (pxD, pyD, pzD) (qxD, qyD, qzD) in 
   felem_seq_as_nat x3 = toDomain_ (xN) /\ felem_seq_as_nat y3 = toDomain_ (yN)  /\ felem_seq_as_nat z3 = toDomain_ (zN)
   
   })
     

let point_add_seq p q = 
    let x1:felem_seq_prime  = Lib.Sequence.sub p 0 4 in 
    let y1:felem_seq_prime  = Lib.Sequence.sub p 4 4 in 
    let z1:felem_seq_prime  = Lib.Sequence.sub p 8 4 in 

    let x2:felem_seq_prime  = Lib.Sequence.sub q 0 4 in 
    let y2:felem_seq_prime  = Lib.Sequence.sub q 4 4 in 
    let z2:felem_seq_prime  = Lib.Sequence.sub q 8 4 in 

  let (u1, u2, s1, s2) = move_from_jacobian_coordinates_seq p q in 
  let flag = point_double_condition_seq u1 u2 s1 s2 z1 z2 in 
  
  if flag then begin  
      let result:point_seq = point_double_seq p in 
	let x3 = Lib.Sequence.sub result 0 4 in 
	let y3 = Lib.Sequence.sub result 4 4 in 
	let z3 = Lib.Sequence.sub result 8 4 in 
      lemma_xToSpecification (fromDomain_ (felem_seq_as_nat x1)) (fromDomain_ (felem_seq_as_nat y1)) (fromDomain_ (felem_seq_as_nat z1)) (fromDomain_ (felem_seq_as_nat x2)) (fromDomain_ (felem_seq_as_nat y2)) (fromDomain_ (felem_seq_as_nat z2)) u1 u2 s1 s2 x3 y3 z3;
      result end
    else 
      begin 
	let (h, r, uh, hCube) = compute_common_params_point_add_seq u1 u2 s1 s2 in 
	let result = point_add_if_second_branch_seq p q u1 u2 s1 s2 r h uh hCube in 
	  let x3 = Lib.Sequence.sub result 0 4 in 
	  let y3 = Lib.Sequence.sub result 4 4 in 
	  let z3 = Lib.Sequence.sub result 8 4 in 
	  lemma_xToSpecification_after_double  (fromDomain_ (felem_seq_as_nat x1)) (fromDomain_ (felem_seq_as_nat y1)) (fromDomain_ (felem_seq_as_nat z1)) (fromDomain_ (felem_seq_as_nat x2)) (fromDomain_ (felem_seq_as_nat y2)) (fromDomain_ (felem_seq_as_nat z2)) u1 u2 s1 s2 h r x3 y3 z3;

	result
	end

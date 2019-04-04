module Hacl.Spec.P256.MontgomeryMultiplication.PointDouble

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

let _point_double p =
  let x, y, z = p in 
  if z = 0 then (x, y, z)
  else begin 
  let s = (4 * x * y * y) % prime in 
  let m = ((-3) * z * z * z * z + 3 * x * x) % prime in 
  let x3 = (m *m - 2 * s) % prime in 
  let y3 = (m * (s - x3) - 8 * y * y * y * y) % prime in 
  let z3 = (2 * y * z) % prime in (x3, y3, z3)
  end



val computeS: px: felem_seq{felem_seq_as_nat px < prime} -> py: felem_seq{felem_seq_as_nat py < prime} -> 
  Lemma ((
    let pxD = fromDomain_ (felem_seq_as_nat px) in let pyD = fromDomain_(felem_seq_as_nat py) in 
    let s = mm_byFour_seq (montgomery_multiplication_seq px (montgomery_multiplication_seq py py)) in 
    felem_seq_as_nat s == toDomain_(4 * pxD * pyD * pyD % prime)))

let computeS px py = 
  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 
  let pxD = fromDomain_ (felem_seq_as_nat px) in 
  let pyD = fromDomain_ (felem_seq_as_nat py) in 
  let a = montgomery_multiplication_seq py py in 
  let b = montgomery_multiplication_seq px a in 
  let s = mm_byFour_seq b in 
  
  assert_by_tactic (pxD * (pyD * pyD) == pxD * pyD * pyD) canon;
  assert_by_tactic (4 * (pxD * pyD * pyD) == 4 * pxD * pyD * pyD) canon;
  
  lemma_mod_mul_distr_r 4 (pxD * pyD * pyD) prime

val computeM: px: felem_seq{felem_seq_as_nat px < prime} -> pz: felem_seq{felem_seq_as_nat pz < prime} -> 
  Lemma ((
   let pxD = fromDomain_ (felem_seq_as_nat px) in let pzD = fromDomain_(felem_seq_as_nat pz) in 
   let m = felem_add_seq (mm_byMinusThree_seq(mm_quatre_seq pz)) (mm_byThree_seq(montgomery_multiplication_seq px px)) in  
  felem_seq_as_nat m = toDomain_ ((((-3) * pzD * pzD * pzD * pzD + 3 * pxD * pxD) % prime)))) 

let computeM px pz = 
  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 

  let pxD = fromDomain_ (felem_seq_as_nat px) in 
  let pzD = fromDomain_ (felem_seq_as_nat pz) in 
  let a = mm_quatre_seq pz in 
  let b = mm_byMinusThree_seq a in 
  let c = montgomery_multiplication_seq px px in 
  let d = mm_byThree_seq c in
  let e = felem_add_seq b d in 

  assert_by_tactic ((-3) * (pzD * pzD * pzD * pzD) == (-3) * pzD * pzD * pzD * pzD) canon;
  assert_by_tactic (3 * (pxD * pxD) == 3 * pxD * pxD) canon;

  lemma_mod_mul_distr_r (-3) (pzD * pzD * pzD * pzD) prime;
  lemma_mod_mul_distr_r 3 (pxD * pxD) prime;
  modulo_distributivity ((-3) * pzD * pzD * pzD * pzD) (3 * pxD * pxD) prime
 

val computeZ3: py: felem_seq{felem_seq_as_nat py < prime} -> pz: felem_seq{felem_seq_as_nat pz < prime} -> 
  Lemma (
    let z3 = mm_byTwo_seq(montgomery_multiplication_seq py pz) in 
    let pyD = fromDomain_ (felem_seq_as_nat py) in let pzD = fromDomain_(felem_seq_as_nat pz) in 
    felem_seq_as_nat z3 = toDomain_(2 * pyD * pzD % prime))

let computeZ3 py pz = 
  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 

  let pyD = fromDomain_ (felem_seq_as_nat py) in 
  let pzD = fromDomain_ (felem_seq_as_nat pz) in 
 
  let a = montgomery_multiplication_seq py pz in 
  let b = mm_byTwo_seq a in 

  assert_by_tactic (2 * (pyD * pzD) = 2 * pyD * pzD) canon


#reset-options "--z3rlimit 100" 

val lemma_xToSpecification: pxD: nat -> pyD: nat -> pzD: nat -> 
  s: felem_seq{felem_seq_as_nat s = toDomain_ (4 * pxD * pyD * pyD % prime)} -> 
  m: felem_seq{felem_seq_as_nat m = toDomain_ ((((-3) * pzD * pzD * pzD * pzD + 3 * pxD * pxD)) % prime)} -> 
  x3: felem_seq{(let mD = fromDomain_ (felem_seq_as_nat m) in let sD = fromDomain_ (felem_seq_as_nat s) in 
    felem_seq_as_nat x3 = toDomain_((mD * mD - 2*sD) % prime))} -> 
  Lemma ((let (xN, yN, zN) = _point_double (pxD, pyD, pzD) in felem_seq_as_nat x3 = toDomain_ (xN)))

let lemma_xToSpecification pxD pyD pzD s m x3  = ()

val lemma_yToSpecification: pxD: nat -> pyD: nat -> pzD: nat ->
  s: felem_seq{felem_seq_as_nat s = toDomain_ (4 * pxD * pyD * pyD % prime)} -> 
  m: felem_seq{felem_seq_as_nat m = toDomain_ ((((-3) * pzD * pzD * pzD * pzD + 3 * pxD * pxD) % prime))} ->
  x3: felem_seq{(let mD = fromDomain_ (felem_seq_as_nat m) in let sD = fromDomain_ (felem_seq_as_nat s) in 
    felem_seq_as_nat x3 = toDomain_((mD * mD - 2*sD) % prime))} -> 
  y3: felem_seq{(let mD = fromDomain_ (felem_seq_as_nat m) in let sD = fromDomain_ (felem_seq_as_nat s) in 
    let x3D = fromDomain_ (felem_seq_as_nat x3) in 
    felem_seq_as_nat y3 = toDomain_ (((mD * (sD - x3D) - (8 * pyD * pyD * pyD * pyD)) % prime)))} -> 
  Lemma(let (xN, yN, zN) = _point_double (pxD, pyD, pzD) in  felem_seq_as_nat y3 = toDomain_ (yN))  

let lemma_yToSpecification pxD pyD pzD s m x3 y3 = ()

val lemma_zToSpecification: pxD: nat ->  pyD: nat -> pzD: nat -> 
  z3: felem_seq{felem_seq_as_nat z3 = toDomain_(2 * pyD * pzD % prime)} -> 
  Lemma (let (xN, yN, zN) = _point_double (pxD, pyD, pzD) in felem_seq_as_nat z3 = toDomain_ (zN))

let lemma_zToSpecification pxD pyD pzD z3 = ()

let isPointAtInfinitySeq p = 
    let a0 = Lib.Sequence.index p 8 in 
    let a1 = Lib.Sequence.index p 9 in 
    let a2 = Lib.Sequence.index p 10 in 
    let a3 = Lib.Sequence.index p 11 in 
    let a_tuple = (a0, a1, a2, a3) in 
    let r = isZero_tuple_b a_tuple in 
    

    let z = Lib.Sequence.sub p 8 4 in 
    let z_seq = felem_seq_as_nat z in 
    assert_norm (modp_inv2 (pow2 256) > 0);
    assert_norm (modp_inv2 (pow2 256) % prime <> 0);
    lemma_multiplication_not_mod_prime z_seq (modp_inv2 (pow2 256));
    r


#reset-options "--z3rlimit 100" 

let copy_point_seq p = p

let point_double_compute_s_m_seq p = 
  let px = Lib.Sequence.sub p 0 4 in 
  let py = Lib.Sequence.sub p 4 4 in 
  let pz = Lib.Sequence.sub p 8 4 in 

  let yy = montgomery_multiplication_seq py py in 
  let xyy = montgomery_multiplication_seq px yy in 
  let s = mm_byFour_seq xyy in 
 
  let zzzz = mm_quatre_seq pz in 
  let minThreeZzzz = mm_byMinusThree_seq zzzz in 
  let xx = montgomery_multiplication_seq px px in 
  let threeXx = mm_byThree_seq xx in 
  let m = felem_add_seq minThreeZzzz threeXx in 
  computeS px py;
  computeM px pz;
  
  (s, m)


let point_double_compute_x3_seq s m = 
  let twoS = mm_byTwo_seq s in 
  let mm = montgomery_multiplication_seq m m in 
  let x3 = felem_sub_seq mm twoS in 
  lemma_minus_distr ((fromDomain_ (felem_seq_as_nat m)) * (fromDomain_ (felem_seq_as_nat m))) (2 * (fromDomain_ (felem_seq_as_nat s))); 
  x3
 
let point_double_compute_y3_seq py x3 s m = 
    let open FStar.Tactics in 
    let open FStar.Tactics.Canon in 

    let yyyy = mm_quatre_seq py in 
    let eightYyyy = mm_byEight_seq yyyy in 
    let sx3 = felem_sub_seq s x3 in 
    let msx3 = montgomery_multiplication_seq m sx3 in 
    let y3 = felem_sub_seq msx3 eightYyyy in 
    
    let mD = fromDomain_ (felem_seq_as_nat m) in 
    let sD = fromDomain_ (felem_seq_as_nat s) in 
    let x3D = fromDomain_ (felem_seq_as_nat x3) in 
    let pyD = fromDomain_ (felem_seq_as_nat py) in 

    assert_by_tactic (8 * (pyD * pyD * pyD * pyD) == 8 * pyD * pyD * pyD * pyD) canon;

    lemma_mod_mul_distr_r mD (sD - x3D) prime;
    lemma_mod_mul_distr_r 8 (pyD * pyD * pyD * pyD) prime;
    lemma_minus_distr (mD * (sD - x3D)) (8 * pyD * pyD * pyD * pyD);
    y3
  

let point_double_seq p =
  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 

  let px = Lib.Sequence.sub p 0 4 in 
  let py = Lib.Sequence.sub p 4 4 in 
  let pz = Lib.Sequence.sub p 8 4 in 

  let p_infinity = isPointAtInfinitySeq p in 
  if p_infinity then 
    begin
      lemmaFromDomainToDomain (felem_seq_as_nat px);
      lemmaFromDomainToDomain (felem_seq_as_nat py);
      lemmaFromDomainToDomain (felem_seq_as_nat pz);
      copy_point_seq p 
    end
  else begin

  let (s, m) = point_double_compute_s_m_seq p in 
  let x3 = point_double_compute_x3_seq s m in 
  let y3 = point_double_compute_y3_seq py x3 s m in
  let pypz = montgomery_multiplication_seq py pz in 
  let z3 = mm_byTwo_seq pypz in 
  
  let r = concat (concat x3 y3) z3 in
  
  computeZ3 py pz;
  
  lemma_xToSpecification (fromDomain_ (felem_seq_as_nat px)) (fromDomain_ (felem_seq_as_nat py)) (fromDomain_ (felem_seq_as_nat pz)) s m x3;
  lemma_yToSpecification (fromDomain_ (felem_seq_as_nat px)) (fromDomain_ (felem_seq_as_nat py)) (fromDomain_ (felem_seq_as_nat pz)) s m x3 y3;
  lemma_zToSpecification (fromDomain_ (felem_seq_as_nat px)) (fromDomain_ (felem_seq_as_nat py)) (fromDomain_ (felem_seq_as_nat pz)) z3;
  r
  end


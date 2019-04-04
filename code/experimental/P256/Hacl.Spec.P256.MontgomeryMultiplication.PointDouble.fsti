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

noextract
val _point_double: p: point_nat -> Tot (r: point_nat {
  let x3, y3, z3 = r in 
  let x, y, z = p in 
  if z = 0 then 
    x3 == x /\ y3 == y /\ z3 == z 
  else begin  
  let s = (4 * x * y * y) % prime in 
  let m = ((-3) * z * z * z * z + 3 * x * x) % prime in 
  x3 == (m * m  - 2 * s) % prime /\
  y3 == (m * (s - x3) - 8 * y * y * y * y) % prime  /\
  z3 == (2 * y * z) % prime
  end
  })

noextract
val isPointAtInfinitySeq : p: point_seq {let z = Lib.Sequence.sub p 8 4 in felem_seq_as_nat z < prime}-> 
  Tot (r: bool {let z = Lib.Sequence.sub p 8 4 in if fromDomain_(felem_seq_as_nat z) = 0 then r == true else r == false})


noextract
val copy_point_seq: p: point_seq -> Tot (r: point_seq)


noextract
val point_double_compute_s_m_seq:  
  p: point_seq
    {let x = Lib.Sequence.sub p 0 4 in let y = Lib.Sequence.sub p 4 4 in let z = Lib.Sequence.sub p 8 4 in felem_seq_as_nat x < prime /\ felem_seq_as_nat y < prime /\ felem_seq_as_nat z < prime} -> 
  Tot (r: tuple2 felem_seq felem_seq{let s, m = r in 
      let px = Lib.Sequence.sub p 0 4 in 
      let py = Lib.Sequence.sub p 4 4 in 
      let pz = Lib.Sequence.sub p 8 4 in   
      let pxD = fromDomain_ (felem_seq_as_nat px) in 
      let pyD = fromDomain_ (felem_seq_as_nat py) in 
      let pzD = fromDomain_ (felem_seq_as_nat pz) in 
      felem_seq_as_nat s == toDomain_(4 * pxD * pyD * pyD % prime) /\
      felem_seq_as_nat m == toDomain_ ((((-3) * pzD * pzD * pzD * pzD + 3 * pxD * pxD) % prime))
  })


noextract
val point_double_compute_x3_seq: s: felem_seq {felem_seq_as_nat s < prime} -> 
  m: felem_seq{felem_seq_as_nat m < prime} -> 
  Tot (x3: felem_seq {
    let mD = fromDomain_ (felem_seq_as_nat m) in let sD = fromDomain_ (felem_seq_as_nat s) in 
    felem_seq_as_nat x3 < prime /\ felem_seq_as_nat x3 = toDomain_ (((mD * mD - 2 * sD) % prime))})

noextract
val point_double_compute_y3_seq: p_y: felem_seq{felem_seq_as_nat p_y < prime} -> x3: felem_seq {felem_seq_as_nat x3 < prime}->  s: felem_seq{felem_seq_as_nat s < prime} -> m: felem_seq{felem_seq_as_nat m < prime} -> Tot (y3: felem_seq {
   let mD = fromDomain_ (felem_seq_as_nat m) in let sD = fromDomain_ (felem_seq_as_nat s) in let x3D = fromDomain_ (felem_seq_as_nat x3) in let pyD = fromDomain_ (felem_seq_as_nat p_y) in
felem_seq_as_nat y3 < prime /\ felem_seq_as_nat y3 = toDomain_ (((mD * (sD - x3D) - (8 * pyD * pyD * pyD * pyD))% prime))})

noextract
val point_double_seq: p: point_seq{let x = Lib.Sequence.sub p 0 4 in let y = Lib.Sequence.sub p 4 4 in let z = Lib.Sequence.sub p 8 4 in 
  felem_seq_as_nat x < prime /\ felem_seq_as_nat y < prime /\ felem_seq_as_nat z < prime} -> 
  Tot (r: point_seq  {
    let x3 = Lib.Sequence.sub r 0 4 in let y3 = Lib.Sequence.sub r 4 4 in let z3 = Lib.Sequence.sub r 8 4 in 
    let x = Lib.Sequence.sub p 0 4 in let y = Lib.Sequence.sub p 4 4 in let z = Lib.Sequence.sub p 8 4 in 
    
    let xD = fromDomain_ (felem_seq_as_nat x) in let yD = fromDomain_ (felem_seq_as_nat y) in let zD = fromDomain_(felem_seq_as_nat z) in 
 
    let (xN, yN, zN) = _point_double (xD, yD, zD) in 
    felem_seq_as_nat x3 = toDomain_ (xN) /\ felem_seq_as_nat y3 = toDomain_ (yN) /\ felem_seq_as_nat z3 = toDomain_ (zN) /\ felem_seq_as_nat x3 < prime /\ felem_seq_as_nat y3 < prime /\ felem_seq_as_nat z3 < prime
    }) 

module Hacl.Impl.P256

open FStar.HyperStack.All
open FStar.HyperStack
open FStar.HyperStack.ST

module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.Curve25519.Field64.Core
module C =  Hacl.Spec.Curve25519.Field64.Core
module D = Hacl.Spec.Curve25519.Field64.Definition
open  Hacl.Spec.P256.Core
open Hacl.Spec.P256.Lemmas
open Hacl.Spec.P256.Definitions
open Hacl.Spec.P256.SolinasReduction
open Hacl.Spec.P256.MontgomeryMultiplication
open Hacl.Spec.P256.MontgomeryMultiplication.PointDouble
open Hacl.Spec.P256.MontgomeryMultiplication.PointAdd



open Lib.Loops
open FStar.Math.Lemmas

module B = LowStar.Buffer
open FStar.Mul

val p256_add: arg1: felem -> arg2: felem ->  out: felem -> 
Stack unit 
(requires (fun h0 ->  
  (let arg1_as_seq = as_seq h0 arg1 in 
  let arg2_as_seq = as_seq h0 arg2 in 
  felem_seq_as_nat arg1_as_seq < prime /\
  felem_seq_as_nat arg2_as_seq < prime /\
  live h0 out /\ live h0 arg1 /\ live h0 arg2)))
(ensures (fun h0 _ h1 -> modifies1 out h0 h1 /\ 
  (*as_nat h1 out == (as_nat h0 arg1 + as_nat h0 arg2) % prime /\ *)
  (let arg1_as_seq = as_seq h0 arg1 in 
  let arg2_as_seq = as_seq h0 arg2 in 
  as_nat h1 out < prime /\
  as_seq h1 out == felem_add_seq arg1_as_seq arg2_as_seq
)))


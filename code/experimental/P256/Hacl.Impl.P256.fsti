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

val point_double: p: point -> result: point ->  tempBuffer: lbuffer uint64 (size 88) -> Stack unit
  (requires fun h -> live h p /\ live h result /\ live h tempBuffer /\ 
    disjoint p result /\ disjoint tempBuffer result /\ disjoint p tempBuffer /\ 
    as_nat h (gsub p (size 8) (size 4)) < prime /\ 
    as_nat h (gsub p (size 0) (size 4)) < prime /\ 
    as_nat h (gsub p (size 4) (size 4)) < prime)
  (ensures fun h0 _ h1 -> modifies2 tempBuffer result h0 h1 /\  
    as_seq h1 result == point_double_seq (as_seq h0 p) /\
    as_nat h1 (gsub p (size 8) (size 4)) < prime /\ 
    as_nat h1 (gsub p (size 0) (size 4)) < prime /\ 
    as_nat h1 (gsub p (size 4) (size 4)) < prime
  )


  
val point_add: p: point -> q: point -> result: point -> tempBuffer: lbuffer uint64 (size 88) -> 
   Stack unit (requires fun h -> live h p /\ live h q /\ live h result /\ live h tempBuffer /\ 
   LowStar.Monotonic.Buffer.all_disjoint [loc p; loc q; loc result; loc tempBuffer] /\
    as_nat h (gsub p (size 8) (size 4)) < prime /\ 
    as_nat h (gsub p (size 0) (size 4)) < prime /\ 
    as_nat h (gsub p (size 4) (size 4)) < prime /\
    as_nat h (gsub q (size 8) (size 4)) < prime /\ 
    as_nat h (gsub q (size 0) (size 4)) < prime /\  
    as_nat h (gsub q (size 4) (size 4)) < prime 
    )
   (ensures fun h0 _ h1 -> modifies2 tempBuffer result h0 h1 /\ as_seq h1 result == point_add_seq (as_seq h0 p) (as_seq h0 q))

module Hacl.Spec.P256.Definitions

open Lib.IntTypes
open FStar.Math.Lemmas
open FStar.Math.Lib

open FStar.HyperStack
open FStar.HyperStack.All
open Lib.Buffer

let felem4 = uint64 * uint64 * uint64 * uint64
let reduction_dt = felem4 * felem4 * felem4 * felem4 * felem4 * felem4 * felem4 * felem4 * felem4

let felem8 = uint64 * uint64  * uint64  * uint64 * uint64 * uint64 * uint64 * uint64
let felem8_32 = uint32 * uint32 * uint32 * uint32 * uint32 * uint32 * uint32 * uint32

let felem9 = uint64 * uint64  * uint64  * uint64 * uint64 * uint64 * uint64 * uint64 * uint64

open FStar.Mul

let prime = pow2 256 - pow2 224 + pow2 192 + pow2 96 -1

(* Montgomery multiplication parameters *)
let s = 64ul
let long = lbuffer uint64 (size 9)

noextract
val as_nat4: f:felem4 -> GTot nat
let as_nat4 f =
  let (s0, s1, s2, s3) = f in
  v s0 + v s1 * pow2 64 + v s2 * pow2 64 * pow2 64 +
  v s3 * pow2 64 * pow2 64 * pow2 64

noextract
val wide_as_nat4: f:felem8 -> GTot nat
let wide_as_nat4 f =
  let (s0, s1, s2, s3, s4, s5, s6, s7) = f in
  v s0 + v s1 * pow2 64 + v s2 * pow2 64 * pow2 64 +
  v s3 * pow2 64 * pow2 64 * pow2 64 +
  v s4 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
  v s5 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
  v s6 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
  v s7 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64


noextract
val as_nat9: f: felem9 -> GTot nat 
let as_nat9 f = 
  let (s0, s1, s2, s3, s4, s5, s6, s7, s8) = f in
  v s0 + v s1 * pow2 64 + v s2 * pow2 64 * pow2 64 +
  v s3 * pow2 64 * pow2 64 * pow2 64 +
  v s4 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
  v s5 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
  v s6 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
  v s7 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
  v s8 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 


noextract
let long_as_nat (h:mem) (e:long) : GTot nat =
  let open Lib.Sequence in 
  let s = as_seq h e in
  let s0 = s.[0] in
  let s1 = s.[1] in
  let s2 = s.[2] in
  let s3 = s.[3] in
  let s4 = s.[4] in
  let s5 = s.[5] in
  let s6 = s.[6] in
  let s7 = s.[7] in
  let s8 = s.[8] in 
  as_nat9 (s0, s1, s2, s3, s4, s5, s6, s7, s8)
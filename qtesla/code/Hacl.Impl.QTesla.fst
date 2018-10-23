module Hacl.Impl.QTesla

open FStar.HyperStack.All
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.PQ.Buffer
open Lib.Endianness

open Hacl.Impl.QTesla.Params

module B  = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack

module LSeq = Lib.Sequence

module S    = Spec.QTesla

let crypto_randombytes = 32
let crypto_seedbytes = 32
let crypto_c_bytes = 32

type elem = uint64
//val uelem: #intsize:m_inttype{elem == uint_t intsize} -> n:nat{n <= maxint intsize} -> u:elem{uint_v #intsize u == n}
let uelem v = u64 v // TODO: Can the underlying size of elem be extracted and this function parameterized?

type poly (n:size_t) = lbuffer elem (v n)
type poly_k (n:size_t) (k:size_t) = lbuffer (poly n) (v k) 

val qtesla_keygen:
    pk: B.buffer uint8
  -> sk: B.buffer uint8
  -> Stack unit
    (requires fun h -> live h pk /\ live h sk /\ disjoint pk sk)
    //(ensures fun h0 _ h1 -> modifies (loc_buffer pk) h0 h1 /\ modifies (loc_buffer sk) h0 h1)
    (ensures fun h0 _ h1 -> True)

let qtesla_keygen pk sk =
  push_frame();
//  let randomness = create (size crypto_randombytes) (u8 0) in
//  let randomness_extended = create (size ((params_k+3)*crypto_seedbytes)) (u8 0) in
  let s = create #_ #1024 (size params_n) (u64 0) in
  pop_frame()
  

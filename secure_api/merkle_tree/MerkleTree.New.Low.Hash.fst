module MerkleTree.New.Low.Hash

open EverCrypt
open EverCrypt.Helpers
open EverCrypt.AutoConfig

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module MHS = FStar.Monotonic.HyperStack
module HH = FStar.Monotonic.HyperHeap

module EHS = EverCrypt.Hash
module S = FStar.Seq

module R = Low.Regional
module B = LowStar.Buffer.Generic

module High = MerkleTree.New.High

// 32-bit indices and sizes
type hash = B.buffer #32 uint8_t

// let hash_size = UInt64.uint_to_t (UInt32.v (EHS.tagLen EHS.SHA256))
let hash_size = UInt32.v (EHS.tagLen EHS.SHA256)

val hash_cfg: EverCrypt.AutoConfig.impl -> HST.St unit
let hash_cfg i =
  EverCrypt.AutoConfig.init (EverCrypt.AutoConfig.Prefer i)

val hash_region_of:
  v:hash -> GTot HH.rid
let hash_region_of v =
  B.frameOf v

val hash_dummy: unit -> Tot hash
let hash_dummy _ = B.null

val hash_r_inv: h:HS.mem -> v:hash -> GTot Type0
let hash_r_inv h v =
  B.live h v /\ B.freeable v /\
  B.len v = hash_size

val hash_r_inv_reg:
  h:HS.mem -> v:hash ->
  Lemma (requires (hash_r_inv h v))
  (ensures (MHS.live_region h (hash_region_of v)))
let hash_r_inv_reg h v = ()

val hash_repr: Type0
let hash_repr = High.hash

val hash_r_repr:
  h:HS.mem -> v:hash{hash_r_inv h v} -> GTot hash_repr
let hash_r_repr h v = B.as_seq h v

val hash_r_sep:
  v:hash -> p:B.loc -> h0:HS.mem -> h1:HS.mem ->
  Lemma (requires (hash_r_inv h0 v /\
      B.loc_disjoint
        (B.loc_all_regions_from false
          (hash_region_of v)) p /\
      B.modifies p h0 h1))
  (ensures (hash_r_inv h1 v /\
     hash_r_repr h0 v == hash_r_repr h1 v))
let hash_r_sep v p h0 h1 =
  assert (B.loc_includes (B.loc_all_regions_from false (hash_region_of v))
           (B.loc_buffer v));
  B.modifies_buffer_elim v p h0 h1

val hash_irepr: Ghost.erased hash_repr
let hash_irepr =
  Ghost.hide (S.create hash_size 0uy)

val hash_r_init_p: v:hash -> GTot Type0
let hash_r_init_p v = True

val hash_r_init:
  r:R.erid ->
  HST.ST hash
    (requires (fun h0 -> true))
    (ensures (fun h0 v h1 ->
      Set.subset (Map.domain (MHS.get_hmap h0))
                 (Map.domain (MHS.get_hmap h1)) /\
      B.modifies B.loc_none h0 h1 /\
      hash_r_init_p v /\
      hash_r_inv h1 v /\
      hash_region_of v = r /\
      hash_r_repr h1 v == Ghost.reveal hash_irepr))
let hash_r_init r =
  B.malloc r 0uy hash_size

val hash_r_free:
  v:hash ->
  HST.ST unit
    (requires (fun h0 -> hash_r_inv h0 v))
    (ensures (fun h0 _ h1 ->
      B.modifies (B.loc_all_regions_from false (hash_region_of v)) h0 h1))
let hash_r_free v =
  B.free v

val hash_copy:
  src:hash -> dst:hash ->
  HST.ST unit
    (requires (fun h0 ->
      hash_r_inv h0 src /\ hash_r_inv h0 dst /\
      HH.disjoint (hash_region_of src) (hash_region_of dst)))
    (ensures (fun h0 _ h1 ->
      B.modifies (B.loc_all_regions_from false (hash_region_of dst)) h0 h1 /\
      hash_r_inv h1 dst /\
      hash_r_repr h1 dst == hash_r_repr h0 src))
let hash_copy src dst =
  B.blit src 0 dst 0 hash_size

// `hash_dummy ()` is is also a trick to extract the C code using KreMLin.
// If we just define and use `hash_dummy` as a constant, then gcc complains with
// the error "initializer element is not a compile-time constant".
val hreg: R.regional hash
let hreg =
  R.Rgl hash_region_of
      (hash_dummy ())
      hash_r_inv
      hash_r_inv_reg
      hash_repr
      hash_r_repr
      hash_r_sep
      hash_irepr
      hash_r_init_p
      hash_r_init
      hash_r_free
      

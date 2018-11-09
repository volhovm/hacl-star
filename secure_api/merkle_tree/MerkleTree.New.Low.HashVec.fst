module MerkleTree.New.Low.HashVec

open FStar.All
open FStar.Integers
open LowStar.Modifies

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module MHS = FStar.Monotonic.HyperStack
module HH = FStar.Monotonic.HyperHeap

module B32 = LowStar.Buffer
module R32 = Low.Regional
module V32 = Low.Vector
module RV32 = Low.RVector
module RVI32 = Low.Regional.Instances

module S = FStar.Seq
module EHS = EverCrypt.Hash

module B = LowStar.Buffer.Generic
open Low.Regional
module V = Low.Vector
module RV = Low.RVector
module RI = Low.Regional.Instances

open MerkleTree.New.Low.Hash
module High = MerkleTree.New.High

val hcpy: RV.copyable hash hreg
let hcpy = RV.Cpy hash_copy

type hash_vec = RV.rvector hreg

val hash_vec_region_of:
  v:hash_vec -> GTot HH.rid
let hash_vec_region_of v = V.frameOf v

private val hash_vec_dummy: hash_vec
private let hash_vec_dummy = V.create_empty hash

val hash_vec_r_inv:
  h:HS.mem -> v:hash_vec -> GTot Type0
let hash_vec_r_inv h v = RV.rv_inv h v

val hash_vec_r_inv_reg:
  h:HS.mem -> v:hash_vec ->
  Lemma (requires (hash_vec_r_inv h v))
  (ensures (MHS.live_region h (hash_vec_region_of v)))
let hash_vec_r_inv_reg h v = ()

private val hash_vec_repr: Type0
private let hash_vec_repr = High.hash_seq

val hash_vec_r_repr:
  h:HS.mem -> v:hash_vec{hash_vec_r_inv h v} -> GTot hash_vec_repr
let hash_vec_r_repr h v =
  RV.as_seq h v

val hash_vec_r_sep:
  v:hash_vec -> p:B.loc -> h0:HS.mem -> h1:HS.mem ->
  Lemma (requires (hash_vec_r_inv h0 v /\
      B.loc_disjoint
        (B.loc_all_regions_from false (hash_vec_region_of v))
        p /\
      B.modifies p h0 h1))
  (ensures (hash_vec_r_inv h1 v /\
     hash_vec_r_repr h0 v == hash_vec_r_repr h1 v))
let hash_vec_r_sep v p h0 h1 =
  RV.rv_inv_preserved v p h0 h1;
  RV.as_seq_preserved v p h0 h1

val hash_vec_irepr: Ghost.erased hash_vec_repr
let hash_vec_irepr =
  Ghost.hide S.empty

val hash_vec_r_init_p: v:hash_vec -> GTot Type0
let hash_vec_r_init_p v =
  V.size_of v = V.sz0

private val hash_vec_r_init:
  r:erid ->
  HST.ST (v:hash_vec)
    (requires (fun h0 -> true))
    (ensures (fun h0 v h1 ->
      Set.subset (Map.domain (MHS.get_hmap h0))
                 (Map.domain (MHS.get_hmap h1)) /\
      B.modifies B.loc_none h0 h1 /\
      hash_vec_r_init_p v /\
      hash_vec_r_inv h1 v /\
      hash_vec_region_of v = r /\
      hash_vec_r_repr h1 v == Ghost.reveal hash_vec_irepr))
private let hash_vec_r_init r =
  let nrid = RV.new_region_ r in
  let ia = Rgl?.dummy hreg in
  V.create_reserve V.sz1 ia r

val hash_vec_r_free:
  v:hash_vec ->
  HST.ST unit
    (requires (fun h0 -> hash_vec_r_inv h0 v))
    (ensures (fun h0 _ h1 ->
      B.modifies (B.loc_all_regions_from false (hash_vec_region_of v)) h0 h1))
let hash_vec_r_free v =  
  RV.free v

val hvreg: regional hash_vec
let hvreg =
  Rgl hash_vec_region_of
      hash_vec_dummy
      hash_vec_r_inv
      hash_vec_r_inv_reg
      hash_vec_repr
      hash_vec_r_repr
      hash_vec_r_sep
      hash_vec_irepr
      hash_vec_r_init_p
      hash_vec_r_init
      hash_vec_r_free


/// Lemmas about hash_vecs

val hash_vec_rv_inv_r_inv:
  h:HS.mem -> hv:hash_vec -> i:V.index_t{i < V.size_of hv} ->
  Lemma (requires (RV.rv_inv h hv))
        (ensures (Rgl?.r_inv hreg h (V.get h hv i)))
let hash_vec_rv_inv_r_inv h hv i = ()

module MerkleTree.New.Low.HashVecVec

module HS = FStar.HyperStack
module HH = FStar.Monotonic.HyperHeap

module S = FStar.Seq

open Low.Regional
module V = Low.Vector
module RV = Low.RVector
module RI = Low.Regional.Instances

open MerkleTree.New.Low.Hash
open MerkleTree.New.Low.HashVec

  
type hash_vv = RV.rvector hvreg

noextract val hvvreg: regional hash_vv
noextract let hvvreg =
  RI.vector_regional hvreg


/// Lemmas about hash_vvs
///
val hash_vv_rv_inv_r_inv:
  h:HS.mem -> hvv:hash_vv ->
  i:V.index_t -> j:V.index_t ->
  Lemma (requires (RV.rv_inv h hvv /\
                  i < V.size_of hvv /\
                  j < V.size_of (V.get h hvv i)))
        (ensures (Rgl?.r_inv hreg h (V.get h (V.get h hvv i) j)))
let hash_vv_rv_inv_r_inv h hvv lv i = ()

val hash_vv_rv_inv_disjoint:
  h:HS.mem -> hvv:hash_vv ->
  i:V.index_t -> j:V.index_t -> drid:HH.rid ->
  Lemma (requires (RV.rv_inv h hvv /\
                  i < V.size_of hvv /\ 
                  j < V.size_of (V.get h hvv i) /\
                  HH.disjoint (Rgl?.region_of hvvreg hvv) drid))
        (ensures (HH.disjoint (Rgl?.region_of hreg (V.get h (V.get h hvv i) j)) drid))
let hash_vv_rv_inv_disjoint h hvv i j drid =
  assert (HH.disjoint (Rgl?.region_of hvreg (V.get h hvv i)) drid);
  assert (RV.rv_inv h (V.get h hvv i));
  assert (HH.disjoint (Rgl?.region_of hreg (V.get h (V.get h hvv i) j)) drid)

val hash_vv_as_seq_get_index:
  h:HS.mem -> hvv:hash_vv -> i:V.index_t -> j:V.index_t ->
  Lemma (requires (RV.rv_inv h hvv /\ 
                  i < V.size_of hvv /\
                  j < V.size_of (V.get h hvv i)))
        (ensures (Rgl?.r_repr hreg h (V.get h (V.get h hvv i) j) ==
                 S.index (S.index (RV.as_seq h hvv) (V.index2nat i)) (V.index2nat j)))
#reset-options "--z3rlimit 20"
let hash_vv_as_seq_get_index h hvv i j = ()

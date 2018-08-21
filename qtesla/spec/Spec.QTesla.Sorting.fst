module Spec.QTesla.Sorting

(* Credit to Nik Swamy for this code *) 
   
module S = FStar.Seq
module L = FStar.List.Tot
module HL = Lib.Sequence

(* The type of a total order on `a` *)
let tot_ord (a:eqtype) = f:(a -> a -> Tot bool) {S.total_order a f}

(* index_mem: 
   A utility function that finds the first index of 
   `x` in `s`, given that we know the `x` is actually contained in `s` *)
let rec index_mem (#a:eqtype) (x:a) (s:S.seq a)
    : Pure nat
           (requires (S.mem x s))
           (ensures (fun i -> i < S.length s /\ S.index s i == x))
           (decreases (S.length s))
    = if S.head s = x then 0
      else 1 + index_mem x (S.tail s)

(* perm_len:
     A lemma that shows that two sequences that are permutations
     of each other also have the same length
*)
#set-options "--max_fuel 1" //a proof optimization: Z3 only needs to unfold the recursive definition of `count` once
let rec perm_len (#a:eqtype) (s1 s2: S.seq a)
  : Lemma (requires (S.permutation a s1 s2))
          (ensures  (S.length s1 == S.length s2))
          (decreases (S.length s1))
  = if S.length s1 = 0 then begin
       if S.length s2 = 0 then ()
       else assert (S.count (Seq.index s2 0) s2 > 0)
    end
    else let s1_hd = Seq.head s1 in
         let s1_tl = Seq.tail s1 in
         assert (S.count s1_hd s1 > 0);
         assert (S.count s1_hd s2 > 0);
         assert (S.length s2 > 0);
         let s2_hd = Seq.head s2 in
         let s2_tl = Seq.tail s2 in
         if s1_hd = s2_hd
         then (assert (S.permutation a s1_tl s2_tl); perm_len s1_tl s2_tl)
         else let i = index_mem s1_hd s2 in
              let s_pfx, s_sfx = S.split_eq s2 i in
              assert (S.equal s_sfx (Seq.append (Seq.create 1 s1_hd) (Seq.tail s_sfx)));
              let s2' = S.append s_pfx (S.tail s_sfx) in
              S.lemma_append_count s_pfx s_sfx;
              S.lemma_append_count (Seq.create 1 s1_hd) (Seq.tail s_sfx);
              S.lemma_append_count s_pfx (S.tail s_sfx);
              assert (S.permutation a s1_tl s2');
              perm_len s1_tl s2'

(* sort_lseq:
   A wrapper of Seq.sortWith which proves that the output sequences
   is a sorted permutation of the input sequence with the same length
*)   
let sort_lseq (#a:eqtype) #n (f:tot_ord a) (s:S.lseq a n) 
  : s':S.lseq a n{S.sorted f s' /\ S.permutation a s s'} =
  S.lemma_seq_sortwith_correctness (L.compare_of_bool f) s;
  let s' = S.sortWith (L.compare_of_bool f) s in
  perm_len s s';
  assert (forall x. FStar.FunctionalExtensionality.feq (L.bool_of_compare (L.compare_of_bool f) x)  (f x));
  assert (FStar.FunctionalExtensionality.feq (L.bool_of_compare (L.compare_of_bool f)) f);
  s'

let sort_seq (#a:eqtype) (f:tot_ord a) (s:S.seq a) 
  : s':S.seq a{S.sorted f s' /\ S.permutation a s s'} =
  S.lemma_seq_sortwith_correctness (L.compare_of_bool f) s;
  let s' = S.sortWith (L.compare_of_bool f) s in
  perm_len s s';
  assert (forall x. FStar.FunctionalExtensionality.feq (L.bool_of_compare (L.compare_of_bool f) x)  (f x));
  assert (FStar.FunctionalExtensionality.feq (L.bool_of_compare (L.compare_of_bool f)) f);
  s'


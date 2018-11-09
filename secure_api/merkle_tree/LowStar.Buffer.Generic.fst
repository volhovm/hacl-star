module LowStar.Buffer.Generic

include LowStar.Monotonic.Buffer.Generic

module P = FStar.Preorder
module G = FStar.Ghost
module Seq = FStar.Seq

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

(*
 * Wrapper over LowStar.Monotonic.Buffer, with trivial preorders
 *   -- functions that take explicit preorder as arguments (e.g. sub etc.)
 *   -- these include allocation functions also
 *)
private let trivial_preorder (a:Type0) :srel a = fun _ _ -> True

type buffer (#n:nat) (a:Type0) = mbuffer #n a (trivial_preorder a) (trivial_preorder a)

unfold let null (#n:nat) (#a:Type0) :buffer a = mnull #n #a #(trivial_preorder a) #(trivial_preorder a)

unfold let gsub (#n:nat) (#a:Type0) = mgsub #n #a #(trivial_preorder a) #(trivial_preorder a) (trivial_preorder a)

unfold let gsub_inj (#n:nat) (#a:Type0) = mgsub_inj #n #a #(trivial_preorder a) #(trivial_preorder a) (trivial_preorder a) (trivial_preorder a)

inline_for_extraction
type pointer (#n:nat) (a:Type0) = b:buffer a{length #n b == 1}

inline_for_extraction
type pointer_or_null (#n:nat) (a:Type0) = b:buffer a{if g_is_null b then True else length #n b == 1}

inline_for_extraction let sub (#n:nat) (#a:Type0) = msub #n #a #(trivial_preorder a) #(trivial_preorder a) (trivial_preorder a)

inline_for_extraction let offset (#n:nat) (#a:Type0) = moffset #n #a #(trivial_preorder a) #(trivial_preorder a) (trivial_preorder a)

unfold let lbuffer (#n:nat) (a:Type0) (len:nat) = lmbuffer #n a (trivial_preorder a) (trivial_preorder a) len

inline_for_extraction let gcmalloc (#n:nat) (#a:Type0) = mgcmalloc #n #a #(trivial_preorder a)

inline_for_extraction let malloc (#n:nat) (#a:Type0) = mmalloc #n #a #(trivial_preorder a)

inline_for_extraction let alloca (#n:nat) (#a:Type0) = malloca #n #a #(trivial_preorder a)

inline_for_extraction let alloca_of_list (#n:nat) (#a:Type0) = malloca_of_list #n #a #(trivial_preorder a)

inline_for_extraction let gcmalloc_of_list (#n:nat) (#a:Type0) = mgcmalloc_of_list #n #a #(trivial_preorder a)

module L = FStar.List.Tot

unfold
let assign_list_t (#n:nat) #a (l: list a) = (b: buffer a) -> HST.Stack unit
  (requires (fun h0 ->
    live h0 b /\
    length b = L.length l))
  (ensures (fun h0 _ h1 ->
    live h1 b /\
    (modifies (loc_buffer b) h0 h1) /\
    as_seq #n h1 b == Seq.seq_of_list l))

let rec assign_list (#n:nat) #a (l: list a): assign_list_t l
= fun b ->
  match l with
  | [] ->
      let h = HST.get () in
      assert (length b = 0);
      assert (Seq.length (as_seq h b) = 0);
      assert (Seq.equal (as_seq h b) (Seq.empty #a));
      assert (Seq.seq_of_list [] `Seq.equal` Seq.empty #a)
  | hd :: tl ->
      let b_hd = sub b (UInt.zero n) (UInt.one n) in
      let b_tl = offset b (UInt.one n) in
      let h = HST.get () in
      upd b_hd (UInt.zero n) hd;
      let h0 = HST.get () in
      assign_list tl b_tl;
      let h1 = HST.get () in
      assert (as_seq h1 b_hd == as_seq h0 b_hd);
      assert (get h1 b_hd 0 == hd);
      assert (as_seq h1 b_tl == Seq.seq_of_list tl);
      assert (Seq.equal (as_seq h1 b) (Seq.append (as_seq h1 b_hd) (as_seq h1 b_tl)));
      assert ((Seq.seq_of_list l) == (Seq.cons hd (Seq.seq_of_list tl)))

module LowStar.Buffer.Generic

include LowStar.Monotonic.Buffer.Generic

module Seq = FStar.Seq
module HST = FStar.HyperStack.ST

(*
 * Wrapper over LowStar.Monotonic.Buffer, with trivial preorders
 *   -- functions that take explicit preorder as arguments (e.g. sub etc.)
 *   -- these include allocation functions also
 *)
private let trivial_preorder (a:Type0) :srel a = fun _ _ -> True

type buffer (a:Type0) (st:eqtype) = mbuffer a st (trivial_preorder a) (trivial_preorder a)

unfold let null (#a:Type0) (#st:eqtype) :buffer a st = mnull #a #st #(trivial_preorder a) #(trivial_preorder a)

unfold let gsub (#a:Type0) (#st:eqtype) = mgsub #a #st #(trivial_preorder a) #(trivial_preorder a) (trivial_preorder a)

unfold let gsub_inj (#a:Type0) (#st:eqtype) = mgsub_inj #a #st #(trivial_preorder a) #(trivial_preorder a) (trivial_preorder a) (trivial_preorder a)

[@unifier_hint_injective]
inline_for_extraction
type pointer (a:Type0) (st:eqtype) = b:buffer a st{length b == 1}

inline_for_extraction
type pointer_or_null (a:Type0) (st:eqtype) = b:buffer a st{if g_is_null b then True else length b == 1}

inline_for_extraction let sub (#a:Type0) (#st:eqtype) = msub #a #st #(trivial_preorder a) #(trivial_preorder a) (trivial_preorder a)

inline_for_extraction let offset (#a:Type0) (#st:eqtype) = moffset #a #st #(trivial_preorder a) #(trivial_preorder a) (trivial_preorder a)

unfold let lbuffer (a:Type0) (#st:eqtype) (len:nat) = lmbuffer a st (trivial_preorder a) (trivial_preorder a) len

inline_for_extraction let gcmalloc (#a:Type0) (#st:eqtype) = mgcmalloc #a #st #(trivial_preorder a)

inline_for_extraction let malloc (#a:Type0) (#st:eqtype) = mmalloc #a #st #(trivial_preorder a)

inline_for_extraction let alloca (#a:Type0) (#st:eqtype) = malloca #a #st #(trivial_preorder a)

inline_for_extraction let alloca_of_list (#a:Type0) (#st:eqtype) = malloca_of_list #a #st #(trivial_preorder a)

inline_for_extraction let gcmalloc_of_list (#a:Type0) (#st:eqtype) = mgcmalloc_of_list #a #st #(trivial_preorder a)

module L = FStar.List.Tot

unfold
let assign_list_t #a #st (l: list a) = (b: buffer a st) -> HST.Stack unit
  (requires (fun h0 ->
    live h0 b /\
    length b = L.length l))
  (ensures (fun h0 _ h1 ->
    live h1 b /\
    (modifies (loc_buffer b) h0 h1) /\
    as_seq h1 b == Seq.seq_of_list l))

let rec assign_list #a (l: list a): assign_list_t l
= fun b ->
  match l with
  | [] ->
      let h = HST.get () in
      assert (length b = 0);
      assert (Seq.length (as_seq h b) = 0);
      assert (Seq.equal (as_seq h b) (Seq.empty #a));
      assert (Seq.seq_of_list [] `Seq.equal` Seq.empty #a)
  | hd :: tl ->
      let b_hd = sub b (index_zero b) (size_one b) in
      let b_tl = offset b 1UL in
      let h = HST.get () in
      upd b_hd 0UL hd;
      let h0 = HST.get () in
      assign_list tl b_tl;
      let h1 = HST.get () in
      modifies_buffer_elim b_hd (loc_buffer b_tl) h0 h1;
      assert (as_seq h1 b_hd == as_seq h0 b_hd);
      assert (get h1 b_hd 0 == hd);
      assert (as_seq h1 b_tl == Seq.seq_of_list tl);
      assert (Seq.equal (as_seq h1 b) (Seq.append (as_seq h1 b_hd) (as_seq h1 b_tl)));
      assert ((Seq.seq_of_list l) == (Seq.cons hd (Seq.seq_of_list tl)))

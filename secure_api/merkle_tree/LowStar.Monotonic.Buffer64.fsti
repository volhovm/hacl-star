module LowStar.Monotonic.Buffer64

module P = FStar.Preorder
module G = FStar.Ghost
module U64 = FStar.UInt64
module Seq = FStar.Seq

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

module LMB = LowStar.Monotonic.Buffer

(* Most comments are taken from the Low* tutorial at:
   https://fstarlang.github.io/lowstar/html/LowStar.html
 *)

(* Shorthand for preorder over sequences *)
unfold let srel (a:Type0) = Preorder.preorder (Seq.seq a)


/// Low* buffers
/// ==============
///
/// The workhorse of Low*, this module allows modeling C arrays on the
/// stack and in the heap.  At compilation time, KreMLin implements
/// buffers using C arrays, i.e. if Low* type ``t`` is translated into C
/// type ``u``, then Low* type ``buffer t`` is translated to C type ``u*``.
///
/// The type is indexed by two preorders:
/// rrel is the preorder with which the buffer is initially created
/// rel  is the preorder of the current buffer (which could be a sub-buffer of the original one)
///
/// The buffer contents are constrained to evolve according to rel

(*
 * rrel is part of the type for technical reasons
 * If we make it part of the implementation of the buffer type,
 * it bumps up the universe of buffer itself by one,
 * which is too restrictive (e.g. no buffers of buffers)
 *
 * We expect that clients will rarely work with this directly
 * Most of the times, they will use wrappers such as buffer, immutable buffer etc.
 *)
val mbuffer (a:Type0) (rrel rel:srel a) :Tot Type0

/// The C ``NULL`` pointer is represented as the Low* ``null`` buffer. For
/// any given type, there is exactly one ``null`` buffer of this type,
/// just like there is exactly one C ``NULL`` pointer of any given type.
///
/// The nullity test ``g_is_null`` is ghost, for proof purposes
/// only. The corresponding stateful nullity test is ``is_null``, see
/// below.

(* FIXME: The nullity test for proof purposes is currently expressed
   as a ghost predicate, `g_is_null`, but it is scheduled to be
   replaced with equality with `null` *)

val g_is_null (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) :GTot bool

val mnull (#a:Type0) (#rrel #rel:srel a) :Tot (b:mbuffer a rrel rel {g_is_null b})

val null_unique (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) :Lemma (g_is_null b <==> b == mnull)

/// ``unused_in b h`` holds only if buffer ``b`` has not been allocated
/// yet.

val unused_in (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) (h:HS.mem) :GTot Type0


/// ``live h b`` holds if, and only if, buffer ``b`` is currently
/// allocated in ``h`` and has not been deallocated yet.
///
/// This predicate corresponds to the C notion of "lifetime", and as
/// such, is a prerequisite for all stateful operations on buffers
/// (see below), per the C standard:
///
///   If an object is referred to outside of its lifetime, the
///   behavior is undefined.
///
///   -- ISO/IEC 9899:2011, Section 6.2.4 paragraph 2
///
/// By contrast, it is not required for the ghost versions of those
/// operators.

val live (#a:Type0) (#rrel #rel:srel a) (h:HS.mem) (b:mbuffer a rrel rel) :GTot Type0


/// The null pointer is always live.

val live_null (a:Type0) (rrel rel:srel a) (h:HS.mem) :Lemma (live h (mnull #a #rrel #rel))

let live_is_null (#a:Type0) (#rrel #rel:srel a) (h:HS.mem) (b:mbuffer a rrel rel)
  :Lemma (requires (g_is_null b == true))
         (ensures (live h b))
         [SMTPat (live h b)]
  = null_unique b;
    live_null a rrel rel h

/// A live buffer has already been allocated.

val live_not_unused_in (#a:Type0) (#rrel #rel:srel a) (h:HS.mem) (b:mbuffer a rrel rel)
  :Lemma (requires (live h b /\ b `unused_in` h)) (ensures False)


/// If two memories have equal domains, then liveness in one implies liveness in the other

val lemma_live_equal_mem_domains (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) (h0 h1:HS.mem)
  :Lemma (requires (HST.equal_domains h0 h1 /\ live h0 b))
         (ensures  (live h1 b))
	 [SMTPat (HST.equal_domains h0 h1); SMTPat (live h1 b)]


(* FIXME: the following definition is necessary to isolate the pattern
   because of unification. In other words, if we attached the pattern
   to `live_not_unused_in`, then we would not be able to use
   `FStar.Classical.forall_intro_`n and
   `FStar.Classical.move_requires` due to unification issues.  Anyway,
   we plan to isolate patterns in a separate module to clean up the Z3
   context.
 *)

let live_not_unused_in' (#a:Type0) (#rrel #rel:srel a) (h:HS.mem) (b:mbuffer a rrel rel)
  :Lemma (requires (live h b /\ b `unused_in` h))
         (ensures False)
         [SMTPat (live h b); SMTPat (b `unused_in` h)]
  = live_not_unused_in h b


/// Buffers live in the HyperStack model, which is an extension of
/// the HyperHeap model, a hierarchical memory model that divides the
/// heap into a tree of regions. This coarse-grained separation
/// allows the programmer to state modifies clauses at the level of
/// regions, rather than on individual buffers.
///
/// The HyperHeap memory model is described:
///  - in the 2016 POPL paper: https://www.fstar-lang.org/papers/mumon/
///  - in the relevant section of the F* tutorial: http://www.fstar-lang.org/tutorial/
///
/// ``frameOf b`` returns the identifier of the region in which the
/// buffer ``b`` lives.

val frameOf (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) :Tot HS.rid


/// ``as_addr b`` returns the abstract address of the buffer in its
/// region, as an allocation unit: two buffers that are allocated
/// separately in the same region will actually have different
/// addresses, but a sub-buffer of a buffer will actually have the
/// same address as its enclosing buffer.

val as_addr (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) :GTot nat


/// A buffer is unused if, and only if, its address is unused.

val unused_in_equiv (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) (h:HS.mem)
  :Lemma (unused_in b h <==>
          (HS.live_region h (frameOf b) ==> as_addr b `Heap.addr_unused_in` (Map.sel (HS.get_hmap h) (frameOf b))))


/// If a buffer is live, then so is its region.

val live_region_frameOf (#a:Type0) (#rrel #rel:srel a) (h:HS.mem) (b:mbuffer a rrel rel)
  :Lemma (requires (live h b))
         (ensures (HS.live_region h (frameOf b)))
         [SMTPatOr [
	     [SMTPat (live h b)];
             [SMTPat (HS.live_region h (frameOf b))];
         ]]


/// The length of a buffer ``b`` is available as a machine integer ``len
/// b`` or as a mathematical integer ``length b``, but both in ghost
/// (proof) code only: just like in C, one cannot compute the length
/// of a buffer at run-time.

val len (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) :GTot U64.t

let length (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) :GTot nat = U64.v (len b)


/// The null pointer has length 0.

val len_null (a:Type0) (rrel rel:srel a) :Lemma (len (mnull #a #rrel #rel) == 0UL)

let length_null_1 (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel)
  :Lemma (requires (length b =!= 0)) (ensures (g_is_null b == false))
         [SMTPat (length b)]
  = len_null a rrel rel;
    null_unique b

let length_null_2 (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel)
  :Lemma (requires (g_is_null b == true)) (ensures (length b == 0))
         [SMTPat (g_is_null b)]
  = len_null a rrel rel;
    null_unique b


/// For functional correctness, buffers are reflected at the proof
/// level using sequences, via ``as_seq b h``, which returns the
/// contents of a given buffer ``b`` in a given heap ``h``. If ``b`` is not
/// live in ``h``, then the result is unspecified.

(* TODO: why not return a lseq and remove length_as_seq lemma? *)
val as_seq (#a:Type0) (#rrel #rel:srel a) (h:HS.mem) (b:mbuffer a rrel rel) :GTot (Seq.seq a)


/// The contents of a buffer ``b`` has the same length as ``b`` itself.

val length_as_seq (#a:Type0) (#rrel #rel:srel a) (h:HS.mem) (b:mbuffer a rrel rel)
  :Lemma (Seq.length (as_seq h b) == length b)
         [SMTPat (Seq.length (as_seq h b))]


/// ``get`` is an often-convenient shorthand to index the value of a
/// given buffer in a given heap, for proof purposes.


let get (#a:Type0) (#rrel #rel:srel a) (h:HS.mem) (p:mbuffer a rrel rel) (i:nat)
  :Ghost a (requires (i < length p)) (ensures (fun _ -> True))
  = Seq.index (as_seq h p) i

/// Before defining sub-buffer related API, we need to define the notion of "compatibility"
///
///
/// Sub-buffers can be taken at a different preorder than their parent buffers
/// But we need to ensure that the changes to the sub-buffer are compatible with the preorder
/// of the parent buffer, and vice versa.

(*
 * The quantifiers are fiercely guarded, so if you are working directly with them,
 * you may have to write additional asserts as triggers
 *)
[@"opaque_to_smt"]
unfold let compatible_sub
  (#a:Type0) (#rrel #rel:srel a)
  (b:mbuffer a rrel rel) (i:U64.t) (len:U64.t{U64.v i + U64.v len <= length b}) (sub_rel:srel a)
  = (forall (s1 s2:Seq.seq a).{:pattern (rel s1 s2);
                                   (sub_rel (Seq.slice s1 (U64.v i) (U64.v i + U64.v len))
			                    (Seq.slice s2 (U64.v i) (U64.v i + U64.v len)))}  //for any two sequences s1 and s2
                         (Seq.length s1 == length b /\ Seq.length s2 == length b /\ rel s1 s2) ==>  //that have lengths same as b, and are related by the preorder rel
		         (sub_rel (Seq.slice s1 (U64.v i) (U64.v i + U64.v len))
			          (Seq.slice s2 (U64.v i) (U64.v i + U64.v len)))) /\  //their slices [i, i + len) should be related by the preorder sub_rel,
    (forall (s s2:Seq.seq a).{:pattern (sub_rel (Seq.slice s (U64.v i) (U64.v i + U64.v len)) s2);
                                  (rel s (Seq.replace_subseq s (U64.v i) (U64.v i + U64.v len) s2))} //for any two sequences s and s2
                        (Seq.length s == length b /\ Seq.length s2 == U64.v len /\  //such that s has length same as b and s2 has length len
                         sub_rel (Seq.slice s (U64.v i) (U64.v i + U64.v len)) s2) ==>  //and the slice [i, i + len) of s is related to s2 by sub_rel,
  		        (rel s (Seq.replace_subseq s (U64.v i) (U64.v i + U64.v len) s2)))  //if we replace the slice [i, i + len) in s by s2, then s and the resulting buffer should be related by rel

/// ``gsub`` is the way to carve a sub-buffer out of a given
/// buffer. ``gsub b i len`` return the sub-buffer of ``b`` starting from
/// offset ``i`` within ``b``, and with length ``len``. Of course ``i`` and
/// ``len`` must fit within the length of ``b``.
///
/// Further the clients can attach a preorder with the subbuffer (sub_rel),
/// provided it is compatible
///
/// ``gsub`` is the ghost version, for proof purposes. Its stateful
/// counterpart is ``sub``, see below.

val mgsub (#a:Type0) (#rrel #rel:srel a) (sub_rel:srel a)
  (b:mbuffer a rrel rel) (i:U64.t) (len:U64.t)
  :Ghost (mbuffer a rrel sub_rel)
         (requires (U64.v i + U64.v len <= length b /\ compatible_sub b i len sub_rel))
	 (ensures (fun _ -> True))

// goffset

/// A buffer is live exactly at the same time as all of its sub-buffers.

val live_gsub (#a:Type0) (#rrel #rel:srel a)
  (h:HS.mem) (b:mbuffer a rrel rel) (i:U64.t) (len:U64.t) (sub_rel:srel a)
  :Lemma (requires (U64.v i + U64.v len <= length b /\ compatible_sub b i len sub_rel))
         (ensures  (live h (mgsub sub_rel b i len) <==> live h b))
         [SMTPatOr [
             [SMTPat (live h (mgsub sub_rel b i len))];
             [SMTPat (live h b); SMTPat (mgsub sub_rel b i len);]
         ]]


val gsub_is_null (#a:Type0) (#rrel #rel:srel a)
  (b:mbuffer a rrel rel) (i:U64.t) (len:U64.t) (sub_rel:srel a)
  :Lemma (requires (U64.v i + U64.v len <= length b /\ compatible_sub b i len sub_rel))
         (ensures (g_is_null (mgsub sub_rel b i len) <==> g_is_null b))
         [SMTPat (g_is_null (mgsub sub_rel b i len))]


/// The length of a sub-buffer is exactly the one provided at ``gsub``.


val len_gsub (#a:Type0) (#rrel #rel:srel a)
  (b:mbuffer a rrel rel) (i:U64.t) (len':U64.t) (sub_rel:srel a)
  :Lemma (requires (U64.v i + U64.v len' <= length b /\ compatible_sub b i len' sub_rel))
         (ensures (len (mgsub sub_rel b i len') == len'))
         [SMTPatOr [
             [SMTPat (len (mgsub sub_rel b i len'))];
             [SMTPat (length (mgsub sub_rel b i len'))];
         ]]


val frameOf_gsub (#a:Type0) (#rrel #rel:srel a)
  (b:mbuffer a rrel rel) (i:U64.t) (len:U64.t) (sub_rel:srel a)
  :Lemma (requires (U64.v i + U64.v len <= length b /\ compatible_sub b i len sub_rel))
         (ensures (frameOf (mgsub sub_rel b i len) == frameOf b))
  [SMTPat (frameOf (mgsub sub_rel b i len))]

val as_addr_gsub (#a:Type0) (#rrel #rel:srel a)
  (b:mbuffer a rrel rel) (i:U64.t) (len:U64.t) (sub_rel:srel a)
  :Lemma (requires (U64.v i + U64.v len <= length b /\ compatible_sub b i len sub_rel))
         (ensures (as_addr (mgsub sub_rel b i len) == as_addr b))
         [SMTPat (as_addr (mgsub sub_rel b i len))]

val mgsub_inj (#a:Type0) (#rrel #rel:srel a) (sub_rel1 sub_rel2:srel a)
  (b1 b2:mbuffer a rrel rel)
  (i1 i2:U64.t)
  (len1 len2:U64.t)
  :Lemma (requires (U64.v i1 + U64.v len1 <= length b1 /\ compatible_sub b1 i1 len1 sub_rel1 /\
                    U64.v i2 + U64.v len2 <= length b2 /\ compatible_sub b2 i2 len2 sub_rel2 /\
		    mgsub sub_rel1 b1 i1 len1 === mgsub sub_rel2 b2 i2 len2))
         (ensures (len1 == len2 /\ (b1 == b2 ==> i1 == i2) /\ ((i1 == i2 /\ length b1 == length b2) ==> b1 == b2)))


/// Nesting two ``gsub`` collapses into one ``gsub``, transitively.

val gsub_gsub (#a:Type0) (#rrel #rel:srel a)
  (b:mbuffer a rrel rel)
  (i1:U64.t) (len1:U64.t) (sub_rel1:srel a)
  (i2: U64.t) (len2: U64.t) (sub_rel2:srel a)
  :Lemma (requires (U64.v i1 + U64.v len1 <= length b /\ compatible_sub b i1 len1 sub_rel1 /\
                    U64.v i2 + U64.v len2 <= U64.v len1 /\ compatible_sub (mgsub sub_rel1 b i1 len1) i2 len2 sub_rel2))
         (ensures  (compatible_sub b (U64.add i1 i2) len2 sub_rel2 /\
                    mgsub sub_rel2 (mgsub sub_rel1 b i1 len1) i2 len2 == mgsub sub_rel2 b (U64.add i1 i2) len2))
         [SMTPat (mgsub sub_rel2 (mgsub sub_rel1 b i1 len1) i2 len2)]


/// A buffer ``b`` is equal to its "largest" sub-buffer, at index 0 and
/// length ``len b``.

val gsub_zero_length (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel)
  :Lemma (compatible_sub b 0UL (len b) rel /\ b == mgsub rel b 0UL (len b))


/// The contents of a sub-buffer is the corresponding slice of the
/// contents of its enclosing buffer.

val as_seq_gsub (#a:Type0) (#rrel #rel:srel a)
  (h:HS.mem) (b:mbuffer a rrel rel) (i:U64.t) (len:U64.t) (sub_rel:srel a)
  :Lemma (requires (U64.v i + U64.v len <= length b /\ compatible_sub b i len sub_rel))
         (ensures (as_seq h (mgsub sub_rel b i len) == Seq.slice (as_seq h b) (U64.v i) (U64.v i + U64.v len)))
         [SMTPat (as_seq h (mgsub sub_rel b i len))]

/// # The modifies clause
///
/// The modifies clause for regions, references and buffers.
/// ==========================================================
///
/// This module presents the modifies clause, a way to track the set
/// of memory locations modified by a stateful Low* (or even F*)
/// program. The basic principle of modifies clauses is that any
/// location that is disjoint from a set of memory locations modified
/// by an operation is preserved by that operation.
///
/// We start by specifying a monoid of sets of memory locations. From
/// a rough high-level view, ``loc`` is the type of sets of memory
/// locations, equipped with an identity element ``loc_none``,
/// representing the empty set, and an associative and commutative
/// operator, ``loc_union``, representing the union of two sets of
/// memory locations.
///
/// Moreover, ``loc_union`` is idempotent, which is useful to cut SMT
/// matching loops with ``modifies_trans`` and ``modifies_refl`` below.


/// ``loc_buffer b`` is the set of memory locations associated to a buffer ``b``.

val loc_buffer (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) :GTot LMB.loc

val loc_buffer_null (a:Type0) (rrel rel:srel a)
  :Lemma (loc_buffer (mnull #a #rrel #rel) == LMB.loc_none)
         [SMTPat (loc_buffer (mnull #a #rrel #rel))]

unfold let loc_addr_of_buffer (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) :GTot LMB.loc =
  LMB.loc_addresses false (frameOf b) (Set.singleton (as_addr b))

/// If a buffer ``b1`` includes a buffer ``b2`` in the sense of the buffer
/// theory (see ``LowStar.Buffer.includes``), then so are their
/// corresponding sets of memory locations.

val loc_includes_gsub_buffer_r
  (l:LMB.loc)
  (#a:Type0) (#rrel #rel:srel a)
  (b:mbuffer a rrel rel) (i:UInt64.t) (len:UInt64.t) (sub_rel:srel a)
: Lemma (requires (UInt64.v i + UInt64.v len <= (length b) /\
                   compatible_sub b i len sub_rel /\
                   LMB.loc_includes l (loc_buffer b)))
        (ensures  (LMB.loc_includes l (loc_buffer (mgsub sub_rel b i len))))
        [SMTPat (LMB.loc_includes l (loc_buffer (mgsub sub_rel b i len)))]

let loc_includes_gsub_buffer_r' (#a:Type0) (#rrel #rel:srel a)
  (b:mbuffer a rrel rel) (i:UInt64.t) (len:UInt64.t) (sub_rel:srel a)
  :Lemma (requires (UInt64.v i + UInt64.v len <= (length b) /\ compatible_sub b i len sub_rel))
         (ensures  (LMB.loc_includes (loc_buffer b) (loc_buffer (mgsub sub_rel b i len))))
         [SMTPat (mgsub sub_rel b i len)]
  = ()

val loc_includes_gsub_buffer_l (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel)
  (i1:UInt64.t) (len1:UInt64.t) (sub_rel1:srel a)
  (i2:UInt64.t) (len2:UInt64.t) (sub_rel2:srel a)
  :Lemma (requires (UInt64.v i1 + UInt64.v len1 <= (length b) /\
                    UInt64.v i1 <= UInt64.v i2 /\ UInt64.v i2 + UInt64.v len2 <= UInt64.v i1 + UInt64.v len1 /\
		    compatible_sub b i1 len1 sub_rel1 /\ compatible_sub b i2 len2 sub_rel2))
         (ensures  (LMB.loc_includes (loc_buffer (mgsub sub_rel1 b i1 len1)) (loc_buffer (mgsub sub_rel2 b i2 len2))))
         [SMTPat (mgsub sub_rel1 b i1 len1); SMTPat (mgsub sub_rel2 b i2 len2)]

/// If the contents of a buffer are equal in two given heaps, then so
/// are the contents of any of its sub-buffers.

val loc_includes_as_seq (#a:Type0) (#rrel1 #rrel2 #rel1 #rel2:srel a)
  (h1 h2:HS.mem) (larger:mbuffer a rrel1 rel1) (smaller:mbuffer a rrel2 rel2)
  :Lemma (requires (LMB.loc_includes (loc_buffer larger) (loc_buffer smaller) /\
                    as_seq h1 larger == as_seq h2 larger /\
		    (live h1 larger \/ live h1 smaller) /\ (live h2 larger \/ live h2 smaller)))
         (ensures  (as_seq h1 smaller == as_seq h2 smaller))

/// Given a buffer ``b``, if its address is in a set ``s`` of addresses in
/// the region of ``b``, then the set of memory locations corresponding
/// to ``b`` is included in the set of memory locations corresponding to
/// the addresses in ``s`` in region ``r``.
///
/// In particular, the set of memory locations corresponding to a
/// buffer is included in the set of memory locations corresponding to
/// its region and address.

val loc_includes_addresses_buffer (#a:Type0) (#rrel #rel:srel a)
  (preserve_liveness:bool) (r:HS.rid) (s:Set.set nat) (p:mbuffer a rrel rel)
  :Lemma (requires (frameOf p == r /\ Set.mem (as_addr p) s))
         (ensures  (LMB.loc_includes (LMB.loc_addresses preserve_liveness r s) (loc_buffer p)))
         [SMTPat (LMB.loc_includes (LMB.loc_addresses preserve_liveness r s) (loc_buffer p))]

let loc_includes_addresses_buffer' (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel)
  :Lemma (LMB.loc_includes (LMB.loc_addresses true (frameOf b) (Set.singleton (as_addr b))) (loc_buffer b))
         [SMTPat (loc_buffer b)]
  = ()


/// The set of memory locations corresponding to a buffer is included
/// in the set of memory locations corresponding to its region.

val loc_includes_region_buffer (#a:Type0) (#rrel #rel:srel a)
  (preserve_liveness:bool) (s:Set.set HS.rid) (b:mbuffer a rrel rel)
  :Lemma (requires (Set.mem (frameOf b) s))
         (ensures (LMB.loc_includes (LMB.loc_regions preserve_liveness s) (loc_buffer b)))
         [SMTPat (LMB.loc_includes (LMB.loc_regions preserve_liveness s) (loc_buffer b))]

let loc_includes_region_buffer' (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel)
  :Lemma (LMB.loc_includes (LMB.loc_regions true (Set.singleton (frameOf b))) (loc_buffer b))
         [SMTPat (loc_buffer b)]
  = ()

/// Patterns with loc_includes, union on the left

let loc_includes_union_l_buffer
  (s1 s2:LMB.loc)
  (#a:Type0) (#rrel #rel:srel a)
  (b:mbuffer a rrel rel)
  :Lemma (requires (LMB.loc_includes s1 (loc_buffer b) \/ LMB.loc_includes s2 (loc_buffer b)))
         (ensures (LMB.loc_includes (LMB.loc_union s1 s2) (loc_buffer b)))
         [SMTPat (LMB.loc_includes (LMB.loc_union s1 s2) (loc_buffer b))]
  = LMB.loc_includes_union_l s1 s2 (loc_buffer b)

val loc_disjoint_gsub_buffer (#a:Type0) (#rrel:srel a) (#rel:srel a)
  (b:mbuffer a rrel rel)
  (i1:UInt64.t) (len1:UInt64.t) (sub_rel1:srel a)
  (i2:UInt64.t) (len2:UInt64.t) (sub_rel2:srel a)
  :Lemma (requires (UInt64.v i1 + UInt64.v len1 <= (length b) /\
                    UInt64.v i2 + UInt64.v len2 <= (length b) /\
		    compatible_sub b i1 len1 sub_rel1 /\ compatible_sub b i2 len2 sub_rel2 /\
		    (UInt64.v i1 + UInt64.v len1 <= UInt64.v i2 \/
                     UInt64.v i2 + UInt64.v len2 <= UInt64.v i1)))
         (ensures  (LMB.loc_disjoint (loc_buffer (mgsub sub_rel1 b i1 len1)) (loc_buffer (mgsub sub_rel2 b i2 len2))))
         [SMTPat (mgsub sub_rel1 b i1 len1); SMTPat (mgsub sub_rel2 b i2 len2)]

/// If a buffer ``b`` is disjoint from a set ``p`` of
/// memory locations which is modified, then its liveness and contents
/// are preserved.

val modifies_buffer_elim (#a:Type0) (#rrel #rel:srel a)
  (b:mbuffer a rrel rel) (p:LMB.loc) (h h':HS.mem)
  :Lemma (requires (LMB.loc_disjoint (loc_buffer b) p /\ live h b /\ LMB.modifies p h h'))
         (ensures  (live h' b /\ (as_seq h b == as_seq h' b)))

val address_liveness_insensitive_buffer (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel)
  :Lemma (LMB.address_liveness_insensitive_locs `LMB.loc_includes` (loc_buffer b))
         [SMTPat (LMB.address_liveness_insensitive_locs `LMB.loc_includes` (loc_buffer b))]

val region_liveness_insensitive_buffer (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel)
  :Lemma (LMB.region_liveness_insensitive_locs `LMB.loc_includes` (loc_buffer b))
         [SMTPat (LMB.region_liveness_insensitive_locs `LMB.loc_includes` (loc_buffer b))]

val modifies_liveness_insensitive_buffer
  (l1 l2:LMB.loc)
  (h h':HS.mem)
  (#a:Type0) (#rrel #rel:srel a)
  (x:mbuffer a rrel rel)
  :Lemma (requires (LMB.modifies (LMB.loc_union l1 l2) h h' /\ LMB.loc_disjoint l1 (loc_buffer x) /\ LMB.address_liveness_insensitive_locs `LMB.loc_includes` l2 /\ live h x))
         (ensures  (live h' x))

let modifies_liveness_insensitive_buffer_weak
  (l:LMB.loc)
  (h h':HS.mem)
  (#a:Type0) (#rrel #rel:srel a)
  (x:mbuffer a rrel rel)
  :Lemma (requires (LMB.modifies l h h' /\ LMB.address_liveness_insensitive_locs `LMB.loc_includes` l /\ live h x))
         (ensures  (live h' x))
  = modifies_liveness_insensitive_buffer LMB.loc_none l h h' x

val modifies_liveness_insensitive_region_buffer
  (l1 l2:LMB.loc)
  (h h':HS.mem)
  (#a:Type0) (#rrel #rel:srel a)
  (x:mbuffer a rrel rel)
  :Lemma (requires (LMB.modifies (LMB.loc_union l1 l2) h h' /\ LMB.loc_disjoint l1 (loc_buffer x) /\ LMB.region_liveness_insensitive_locs `LMB.loc_includes` l2 /\ HS.live_region h (frameOf x)))
         (ensures  (HS.live_region h' (frameOf x)))
  (* TODO: pattern *)

let modifies_liveness_insensitive_region_buffer_weak
  (l2:LMB.loc)
  (h h':HS.mem)
  (#a:Type0) (#rrel #rel:srel a)
  (x:mbuffer a rrel rel)
  :Lemma (requires (LMB.modifies l2 h h' /\ LMB.region_liveness_insensitive_locs `LMB.loc_includes` l2 /\ HS.live_region h (frameOf x)))
         (ensures  (HS.live_region h' (frameOf x)))
  = modifies_liveness_insensitive_region_buffer LMB.loc_none l2 h h' x

val live_loc_not_unused_in (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) (h:HS.mem)
  :Lemma (requires (live h b))
         (ensures  (LMB.loc_not_unused_in h `LMB.loc_includes` loc_addr_of_buffer b))
         [SMTPat (live h b)]

val unused_in_loc_unused_in (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) (h:HS.mem)
  :Lemma (requires (unused_in b h))
         (ensures  (LMB.loc_unused_in h `LMB.loc_includes` loc_addr_of_buffer b))
         [SMTPat (unused_in b h)]

val modifies_inert_liveness_insensitive_buffer_weak
  (l:LMB.loc)
  (h h':HS.mem)
  (#a:Type0) (#rrel #rel:srel a)
  (x:mbuffer a rrel rel)
  :Lemma (requires (LMB.modifies_inert l h h' /\ LMB.address_liveness_insensitive_locs `LMB.loc_includes` l /\ live h x))
         (ensures (live h' x))
         [SMTPatOr [
             [SMTPat (live h x); SMTPat (LMB.modifies_inert l h h');];
             [SMTPat (live h' x); SMTPat (LMB.modifies_inert l h h');];
         ]]

val modifies_inert_liveness_insensitive_region_buffer_weak
  (l2:LMB.loc)
  (h h':HS.mem)
  (#a:Type0) (#rrel #rel:srel a)
  (x:mbuffer a rrel rel)
  :Lemma (requires (LMB.modifies_inert l2 h h' /\ LMB.region_liveness_insensitive_locs `LMB.loc_includes` l2 /\ HS.live_region h (frameOf x)))
         (ensures  (HS.live_region h' (frameOf x)))
         [SMTPatOr [
             [SMTPat (LMB.modifies_inert l2 h h'); SMTPat (HS.live_region h (frameOf x))];
             [SMTPat (LMB.modifies_inert l2 h h'); SMTPat (HS.live_region h' (frameOf x))];
         ]]

/// Legacy shorthands for disjointness and inclusion of buffers
///

let disjoint (#a1 #a2:Type0) (#rrel1 #rel1:srel a1) (#rrel2 #rel2:srel a2)
  (b1:mbuffer a1 rrel1 rel1) (b2:mbuffer a2 rrel2 rel2) :GTot Type0 =
  LMB.loc_disjoint (loc_buffer b1) (loc_buffer b2)

let includes (#a1 #a2:Type0) (#rrel1 #rel1:srel a1) (#rrel2 #rel2:srel a2)
  (b1:mbuffer a1 rrel1 rel1) (b2:mbuffer a2 rrel2 rel2) :GTot Type0 =
  LMB.loc_includes (loc_buffer b1) (loc_buffer b2) /\
  (g_is_null b1 <==> g_is_null b2)

val disjoint_neq (#a1 #a2:Type0) (#rrel1 #rel1:srel a1) (#rrel2 #rel2:srel a2)
  (b1:mbuffer a1 rrel1 rel1) (b2:mbuffer a2 rrel2 rel2)
  :Lemma (requires (disjoint b1 b2 /\ U64.v (len b1) > 0))
         (ensures (~(b1 === b2)))


/// The liveness of a sub-buffer is exactly equivalent to the liveness
/// of its enclosing buffer.

val includes_live (#a:Type0) (#rrel #rel1 #rel2:srel a)
  (h:HS.mem) (larger:mbuffer a rrel rel1) (smaller:mbuffer a rrel rel2)
  :Lemma (requires (larger `includes` smaller))
         (ensures  (live h larger <==> live h smaller))
         [SMTPatOr [
             [SMTPat (includes larger smaller); SMTPat (live h larger)];
             [SMTPat (includes larger smaller); SMTPat (live h smaller)];
         ]]

val includes_frameOf_as_addr (#a1 #a2:Type0) (#rrel1 #rel1:srel a1) (#rrel2 #rel2:srel a2)
  (larger:mbuffer a1 rrel1 rel1) (smaller:mbuffer a2 rrel2 rel2)
  :Lemma (requires (larger `includes` smaller))
         (ensures (g_is_null larger == g_is_null smaller /\ frameOf larger == frameOf smaller /\ as_addr larger == as_addr smaller))
         [SMTPat (larger `includes` smaller)]

///
/// Useful shorthands for pointers, or maybe-null pointers

inline_for_extraction
type mpointer (a:Type0) (rrel:srel a) (rel:srel a)  =
  b:mbuffer a rrel rel{length b == 1}

inline_for_extraction
type mpointer_or_null (a:Type0) (rrel:srel a) (rel:srel a) =
  b:mbuffer a rrel rel{if g_is_null b then True else length b == 1}

unfold
let deref (#a:Type0) (#rrel #rel:srel a) (h:HS.mem) (x:mpointer a rrel rel) =
  get h x 0


/// Two pointers having different contents are disjoint. This is valid
/// only for pointers, i.e. buffers of size 1.

val pointer_distinct_sel_disjoint
  (#a:Type0) (#rrel1 #rrel2 #rel1 #rel2:srel a)
  (b1:mpointer a rrel1 rel1)
  (b2:mpointer a rrel2 rel2)
  (h:HS.mem)
  :Lemma (requires (live h b1 /\ live h b2 /\ get h b1 0 =!= get h b2 0))
         (ensures  (disjoint b1 b2))

/// The following stateful operations on buffers do not change the
/// memory, but, as required by the C standard, they all require the
/// buffer in question to be live.

/// The nullity test, ``is_null b``, which KreMLin compiles to C as ``b == NULL``.

val is_null (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel)
  :HST.Stack bool (requires (fun h -> live h b))
                  (ensures  (fun h y h' -> h == h' /\ y == g_is_null b))


/// ``sub b i len`` constructs the sub-buffer of ``b`` starting from
/// offset ``i`` with length ``len``. KreMLin extracts this operation as
/// ``b + i`` (or, equivalently, ``&b[i]``.)

val msub (#a:Type0) (#rrel #rel:srel a) (sub_rel:srel a) (b:mbuffer a rrel rel)
  (i:U64.t) (len:U64.t)
  :HST.Stack (mbuffer a rrel sub_rel)
             (requires (fun h -> U64.v i + U64.v len <= length b /\ compatible_sub b i len sub_rel /\ live h b))
             (ensures  (fun h y h' -> h == h' /\ y == mgsub sub_rel b i len))


/// ``offset b i`` construct the tail of the buffer ``b`` starting from
/// offset ``i``, i.e. the sub-buffer of ``b`` starting from offset ``i``
/// with length ``U64.sub (len b) i``. KreMLin compiles it as ``b + i`` or
/// ``&b[i]``.
///
/// This stateful operation cannot be derived from ``sub``, because the
/// length cannot be computed outside of proofs.

val moffset (#a:Type0) (#rrel #rel:srel a) (sub_rel:srel a) (b:mbuffer a rrel rel)
  (i:U64.t)
  :HST.Stack (mbuffer a rrel sub_rel)
             (requires (fun h -> U64.v i <= length b /\ compatible_sub b i (U64.sub (len b) i) sub_rel /\ live h b))
             (ensures  (fun h y h' -> h == h' /\ y == mgsub sub_rel b i (U64.sub (len b) i)))
// goffset


/// ``index b i`` reads the value of ``b`` at offset ``i`` from memory and
/// returns it. KreMLin compiles it as b[i].

val index (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) (i:U64.t)
  :HST.Stack a (requires (fun h -> live h b /\ U64.v i < length b))
               (ensures  (fun h y h' -> h == h' /\ y == Seq.index (as_seq h b) (U64.v i)))


/// The following stateful operations on buffers modify the memory,
/// and, as usual, require the liveness of the buffer.

/// ``g_upd_seq b s h`` updates the entire buffer `b`'s contents in
/// heap `h` to correspond to the sequence `s`

val g_upd_seq (#a:Type0) (#rrel #rel:srel a)
              (b:mbuffer a rrel rel) (s:Seq.lseq a (length b))
	      (h:HS.mem{live h b})
  :GTot HS.mem

val lemma_g_upd_with_same_seq (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) (h:HS.mem)
  :Lemma (requires (live h b)) (ensures (g_upd_seq b (as_seq h b) h == h))

/// A lemma specifying `g_upd_seq` in terms of its effect on the
/// buffer's underlying sequence

val g_upd_seq_as_seq (#a:Type0) (#rrel #rel:srel a)
                     (b:mbuffer a rrel rel)
                     (s:Seq.lseq a (length b))
                     (h:HS.mem{live h b})
  : Lemma (let h' = g_upd_seq b s h in
           (Seq.length s > 0 ==> not (g_is_null b)) /\
           LMB.modifies (loc_buffer b) h h' /\
           live h' b /\
           as_seq h' b == s)

/// ``g_upd b i v h`` updates the buffer `b` in heap `h` at location
/// `i` writing ``v`` there. This is the spec analog of the stateful
/// update `upd` below.

let g_upd (#a:Type0) (#rrel #rel:srel a)
          (b:mbuffer a rrel rel)
          (i:nat{i < length b})
          (v:a)
          (h:HS.mem{live h b})
  : GTot HS.mem
  = g_upd_seq b (Seq.upd (as_seq h b) i v) h

/// ``upd b i v`` writes ``v`` to the memory, at offset ``i`` of
/// buffer ``b``. KreMLin compiles it as ``b[i] = v``.

val upd'
  (#a:Type0) (#rrel #rel:srel a)
  (b:mbuffer a rrel rel)
  (i:U64.t)
  (v:a)
  :HST.Stack unit (requires (fun h -> live h b /\ U64.v i < length b /\
                                   rel (as_seq h b) (Seq.upd (as_seq h b) (U64.v i) v)))
                  (ensures  (fun h _ h' -> h' == g_upd b (U64.v i) v h))

inline_for_extraction
let upd
  (#a:Type0) (#rrel #rel:srel a)
  (b:mbuffer a rrel rel)
  (i:U64.t)
  (v:a)
  : HST.Stack unit (requires (fun h -> live h b /\ U64.v i < length b /\
                                    rel (as_seq h b) (Seq.upd (as_seq h b) (U64.v i) v)))
                   (ensures (fun h _ h' -> (not (g_is_null b)) /\
                                        LMB.modifies (loc_buffer b) h h' /\
                                        live h' b /\
                                        as_seq h' b == Seq.upd (as_seq h b) (U64.v i) v))
  = let h = HST.get () in
    upd' b i v;
    g_upd_seq_as_seq b (Seq.upd (as_seq h b) (U64.v i) v) h

(* FIXME: Comment on `recall` *)

val recallable (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) :GTot Type0

val recallable_null (#a:Type0) (#rrel #rel:srel a)
  :Lemma (recallable (mnull #a #rrel #rel)) [SMTPat (recallable (mnull #a #rrel #rel))]

val recallable_includes (#a1 #a2:Type0) (#rrel1 #rel1:srel a1) (#rrel2 #rel2:srel a2)
  (larger:mbuffer a1 rrel1 rel1) (smaller:mbuffer a2 rrel2 rel2)
  :Lemma (requires (larger `includes` smaller))
         (ensures (recallable larger <==> recallable smaller))
         [SMTPatOr [
             [SMTPat (recallable larger); SMTPat (recallable smaller);];
             [SMTPat (larger `includes` smaller)];
         ]]

val recall (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel)
  :HST.Stack unit (requires (fun _ -> recallable b))
                  (ensures  (fun m0 _ m1 -> m0 == m1 /\ live m1 b))

(*
 * Begin: API for general witness and recall
 *        Clients can witness predicates on the contents of the buffer, and later recall them
 *        Provided the predicates are stable w.r.t. the buffer preorder
 *)

(* Shorthand for predicates of Seq.seq a *)
unfold let spred (a:Type0) = Seq.seq a -> Type0

(*
 * Note the tight patterns on the quantifier, you may need to write additional triggers
 * if you are directly working with them
 *)
unfold let stable_on (#a:Type0) (p:spred a) (rel:srel a) =
  forall (s1 s2:Seq.seq a).{:pattern (p s1); (rel s1 s2); (p s2)} (p s1 /\ rel s1 s2) ==> p s2

(* Clients get this pure token when they witness a predicate *)
val witnessed (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) (p:spred a) :Type0

(*
 * We can only support witness and recall for gc-malloced buffers (i.e. recallable ones)
 * This is not a fundamental limitation, but needs some tweaks to the underlying state model
 *)
val witness_p (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) (p:spred a)
  :HST.ST unit (requires (fun h0      -> p (as_seq h0 b) /\ p `stable_on` rel))
               (ensures  (fun h0 _ h1 -> h0 == h1 /\ b `witnessed` p))

val recall_p (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) (p:spred a)
  :HST.ST unit (requires (fun h0      -> (recallable b \/ live h0 b) /\ b `witnessed` p))
               (ensures  (fun h0 _ h1 -> h0 == h1 /\ live h0 b /\ p (as_seq h0 b)))

(* End: API for general witness and recall *)


/// Deallocation. A buffer that was allocated by ``malloc`` (see below)
/// can be ``free`` d.

val freeable (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) :GTot Type0

val free (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel)
  :HST.ST unit (requires (fun h0 -> live h0 b /\ freeable b))
               (ensures  (fun h0 _ h1 -> (not (g_is_null b)) /\
                                      Map.domain (HS.get_hmap h1) `Set.equal` Map.domain (HS.get_hmap h0) /\
                                      (HS.get_tip h1) == (HS.get_tip h0) /\
                                      LMB.modifies (loc_addr_of_buffer b) h0 h1 /\
                                      HS.live_region h1 (frameOf b)))

val freeable_length (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel)
  :Lemma (requires (freeable b)) (ensures (length b > 0))
         [SMTPat (freeable b)]

val freeable_disjoint (#a1 #a2:Type0) (#rrel1 #rel1:srel a1) (#rrel2 #rel2:srel a2)
  (b1:mbuffer a1 rrel1 rel1) (b2:mbuffer a2 rrel2 rel2)
  :Lemma (requires (freeable b1 /\ length b2 > 0 /\ disjoint b1 b2))
         (ensures (frameOf b1 <> frameOf b2 \/ as_addr b1 <> as_addr b2))

let freeable_disjoint' (#a1 #a2:Type0) (#rrel1 #rel1:srel a1) (#rrel2 #rel2:srel a2)
  (b1:mbuffer a1 rrel1 rel1) (b2:mbuffer a2 rrel2 rel2)
  :Lemma (requires (freeable b1 /\ length b2 > 0 /\ disjoint b1 b2))
         (ensures (LMB.loc_disjoint (loc_addr_of_buffer b1) (loc_addr_of_buffer b2)))
         [SMTPat (freeable b1); SMTPat (disjoint b1 b2)]
  = freeable_disjoint b1 b2

(***** Begin allocation functions *****)


/// Allocation. This is the common postcondition of all allocation
/// operators, which tells that the resulting buffer is fresh, and
/// specifies its initial contents.

(*
 * Allocation functions:
 *   In the return type, we try to give heap-independent postconditions (such as length)
 *   in the refinement of the buffer type (for the usage pattern of top-level buffers)
 *   while heap dependent postconditions are provided in the ensures clause
 *
 *   One unsatisfying aspect is that these functions are duplicated in the wrappers that we write
 *   (e.g. Buffer, Immutablebuffer, etc.)
 *   If we don't duplicate, then the clients may face type inference issues (for preorders)
 *
 *   So, if you change any of the pre- or postcondition, you should change the pre and post spec functions
 *   (such as alloc_post_mem_common etc.), rather than the specs directly

 *   Perhaps we can rely on F* type inference and not write specs explicitly in those wrappers?
 *   Will try that
 *
 *   For memory dependent post, alloc_post_mem_common is the one used by everyone
 *
 *   For heap allocations, the library also provides partial functions that could return null
 *     Clients need to explicitly check for non-nullness when using these functions
 *     Partial function specs use alloc_partial_post_mem_common
 *
 *   NOTE: a useful test for the implementation of partial functions is that
 *         their spec should be valid even when their implementation just returns null
 *)

unfold let lmbuffer (a:Type0) (rrel rel:srel a) (len:nat)
  = b:mbuffer a rrel rel{length b == len /\ not (g_is_null b)}

unfold
let alloc_post_mem_common (#a:Type0) (#rrel #rel:srel a)
  (b:mbuffer a rrel rel) (h0 h1:HS.mem) (s:Seq.seq a)
  = b `unused_in` h0 /\
    live h1 b /\
    Map.domain (HS.get_hmap h1) `Set.equal` Map.domain (HS.get_hmap h0) /\
    (HS.get_tip h1) == (HS.get_tip h0) /\
    LMB.modifies LMB.loc_none h0 h1 /\
    as_seq h1 b == s

(* Return type and post for partial allocation functions *)
unfold let lmbuffer_or_null (a:Type0) (rrel rel:srel a) (len:nat) (r:HS.rid)
  = b:mbuffer a rrel rel{(not (g_is_null b)) ==> (length b == len /\ frameOf b == r)}

unfold let alloc_partial_post_mem_common (#a:Type0) (#rrel #rel:srel a)
  (b:mbuffer a rrel rel) (h0 h1:HS.mem) (s:Seq.seq a)
  = (g_is_null b /\ h0 == h1) \/
    ((not (g_is_null b)) /\ alloc_post_mem_common b h0 h1 s)


unfold let malloc_pre (r:HS.rid) (len:U64.t) = HST.is_eternal_region r /\ U64.v len > 0


/// ``gcmalloc r init len`` allocates a memory-managed buffer of some
/// positive length ``len`` in an eternal region ``r``. Every cell of this
/// buffer will have initial contents ``init``. Such a buffer cannot be
/// freed. In fact, it is eternal: it cannot be deallocated at all.

(*
 * See the Allocation comment above when changing the spec
 *)
val mgcmalloc (#a:Type0) (#rrel:srel a)
  (r:HS.rid) (init:a) (len:U64.t)
  :HST.ST (b:lmbuffer a rrel rrel (U64.v len){frameOf b == r /\ recallable b})
          (requires (fun _       -> malloc_pre r len))
          (ensures  (fun h0 b h1 -> alloc_post_mem_common b h0 h1 (Seq.create (U64.v len) init)))

(*
 * See the Allocation comment above when changing the spec
 *)
inline_for_extraction
let mgcmalloc_partial (#a:Type0) (#rrel:srel a)
  (r:HS.rid) (init:a) (len:U64.t)
  :HST.ST (b:lmbuffer_or_null a rrel rrel (U64.v len) r{recallable b})
          (requires (fun _       -> malloc_pre r len))
          (ensures  (fun h0 b h1 -> alloc_partial_post_mem_common b h0 h1 (Seq.create (U64.v len) init)))
  = mgcmalloc r init len


/// ``malloc r init len`` allocates a hand-managed buffer of some
/// positive length ``len`` in an eternal region ``r``. Every cell of this
/// buffer will have initial contents ``init``. Such a buffer can be
/// freed using ``free`` above. Note that the ``freeable`` permission is
/// only on the whole buffer ``b``, and is not inherited by any of its
/// strict sub-buffers.

(*
 * See the Allocation comment above when changing the spec
 *)
val mmalloc (#a:Type0) (#rrel:srel a)
  (r:HS.rid) (init:a) (len:U64.t)
  :HST.ST (b:lmbuffer a rrel rrel (U64.v len){frameOf b == r /\ freeable b})
          (requires (fun _       -> malloc_pre r len))
          (ensures  (fun h0 b h1 -> alloc_post_mem_common b h0 h1 (Seq.create (U64.v len) init)))

(*
 * See the Allocation comment above when changing the spec
 *)
inline_for_extraction
let mmalloc_partial (#a:Type0) (#rrel:srel a)
  (r:HS.rid) (init:a) (len:U64.t)
  :HST.ST (b:lmbuffer_or_null a rrel rrel (U64.v len) r{(not (g_is_null b)) ==> freeable b})
          (requires (fun _       -> malloc_pre r len))
          (ensures  (fun h0 b h1 -> alloc_partial_post_mem_common b h0 h1 (Seq.create (U64.v len) init)))
  = mmalloc r init len


/// ``alloca init len`` allocates a buffer of some positive length ``len``
/// in the current stack frame. Every cell of this buffer will have
/// initial contents ``init``. Such a buffer cannot be freed
/// individually, but is automatically freed as soon as its stack
/// frame is deallocated by ``HST.pop_frame``.

unfold let alloca_pre (len:U64.t) = U64.v len > 0

(*
 * See the Allocation comment above when changing the spec
 *)
val malloca (#a:Type0) (#rrel:srel a)
  (init:a) (len:U64.t)
  :HST.StackInline (lmbuffer a rrel rrel (U64.v len))
                   (requires (fun _       -> alloca_pre len))
                   (ensures  (fun h0 b h1 -> alloc_post_mem_common b h0 h1 (Seq.create (U64.v len) init) /\
		                          frameOf b == HS.get_tip h0))


/// ``alloca_of_list init`` allocates a buffer in the current stack
/// frame. The initial values of the cells of this buffer are
/// specified by the ``init`` list, which must be nonempty, and of
/// length representable as a machine integer.

unfold let alloca_of_list_pre (#a:Type0) (init:list a) =
  normalize (0 < FStar.List.Tot.length init) /\
  normalize (FStar.List.Tot.length init <= UInt.max_int 32)

(*
 * See the Allocation comment above when changing the spec
 *)
val malloca_of_list (#a:Type0) (#rrel:srel a) (init: list a)
  :HST.StackInline (lmbuffer a rrel rrel (normalize_term (List.Tot.length init)))
                   (requires (fun _      -> alloca_of_list_pre init))
                   (ensures (fun h0 b h1 -> alloc_post_mem_common b h0 h1 (Seq.seq_of_list init) /\
		                         frameOf b == HS.get_tip h0))

unfold let gcmalloc_of_list_pre (#a:Type0) (r:HS.rid) (init:list a) =
  HST.is_eternal_region r /\
  normalize (FStar.List.Tot.length init <= UInt.max_int 32)

(*
 * See the Allocation comment above when changing the spec
 *)
val mgcmalloc_of_list (#a:Type0) (#rrel:srel a) (r:HS.rid) (init:list a)
  :HST.ST (b:lmbuffer a rrel rrel (normalize_term (List.Tot.length init)){frameOf b == r /\ recallable b})
          (requires (fun _       -> gcmalloc_of_list_pre r init))
          (ensures  (fun h0 b h1 -> alloc_post_mem_common b h0 h1 (Seq.seq_of_list init)))

(*
 * See the Allocation comment above when changing the spec
 *)
inline_for_extraction
let mgcmalloc_of_list_partial (#a:Type0) (#rrel:srel a) (r:HS.rid) (init:list a)
  :HST.ST (b:lmbuffer_or_null a rrel rrel (normalize_term (List.Tot.length init)) r{recallable b})
          (requires (fun _       -> gcmalloc_of_list_pre r init))
          (ensures  (fun h0 b h1 -> alloc_partial_post_mem_common b h0 h1 (Seq.seq_of_list init)))

  = mgcmalloc_of_list r init


(***** End allocation functions *****)


/// Derived operations

val blit (#a:Type0) (#rrel1 #rrel2 #rel1 #rel2:srel a)
  (src:mbuffer a rrel1 rel1)
  (idx_src:U64.t)
  (dst:mbuffer a rrel2 rel2)
  (idx_dst:U64.t)
  (len:U64.t)
  :HST.Stack unit (requires (fun h -> live h src /\ live h dst /\ disjoint src dst /\
                                    U64.v idx_src + U64.v len <= length src /\
                                    U64.v idx_dst + U64.v len <= length dst /\
				    rel2 (as_seq h dst)
				         (Seq.replace_subseq (as_seq h dst) (U64.v idx_dst) (U64.v idx_dst + U64.v len)
					                     (Seq.slice (as_seq h src) (U64.v idx_src) (U64.v idx_src + U64.v len)))))
                  (ensures (fun h _ h' -> LMB.modifies (loc_buffer dst) h h' /\
                                        live h' dst /\
                                        Seq.slice (as_seq h' dst) (U64.v idx_dst) (U64.v idx_dst + U64.v len) ==
                                        Seq.slice (as_seq h src) (U64.v idx_src) (U64.v idx_src + U64.v len) /\
                                        Seq.slice (as_seq h' dst) 0 (U64.v idx_dst) ==
                                        Seq.slice (as_seq h dst) 0 (U64.v idx_dst) /\
                                        Seq.slice (as_seq h' dst) (U64.v idx_dst + U64.v len) (length dst) ==
                                        Seq.slice (as_seq h dst) (U64.v idx_dst + U64.v len) (length dst)))

val fill (#t:Type) (#rrel #rel: srel t)
  (b: mbuffer t rrel rel)
  (z:t)
  (len:U64.t)
: HST.Stack unit
  (requires (fun h ->
    live h b /\
    U64.v len <= length b /\
    rel (as_seq h b) (Seq.replace_subseq (as_seq h b) 0 (U64.v len) (Seq.create (U64.v len) z))
  ))
  (ensures  (fun h0 _ h1 ->
    LMB.modifies (loc_buffer b) h0 h1 /\
    live h1 b /\
    Seq.slice (as_seq h1 b) 0 (U64.v len) == Seq.create (U64.v len) z /\
    Seq.slice (as_seq h1 b) (U64.v len) (length b) == Seq.slice (as_seq h0 b) (U64.v len) (length b)
  ))

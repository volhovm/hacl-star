module Low.Vector

open FStar.All
open FStar.Integers
open LowStar.Modifies

module HH = FStar.Monotonic.HyperHeap
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module MHS = FStar.Monotonic.HyperStack
module B = LowStar.Buffer.Generic
module S = FStar.Seq
module U64 = FStar.UInt64

type uint64_t = U64.t

val max_uint64: uint64_t
let max_uint64 = 18446744073709551615UL


/// Abstract vector type

noeq type vector_str (a:Type0) (st:eqtype) =
| Vec: sz:st ->
       cap:st{B.size_at_least cap sz} ->
       vs:B.buffer a st {B.len vs = cap} ->
       vector_str a st

val vector (a:Type0) (st:eqtype) : Tot Type0
let vector a st = vector_str a st

/// Specification

val as_seq:
  HS.mem -> #a:Type -> #st:eqtype-> vec:vector a st ->
  GTot (s:S.seq a{S.length s = B.size2nat (Vec?.sz vec)})
let as_seq h #a #st vec =
  B.as_seq h (B.gsub (Vec?.vs vec) (B.index_zero (Vec?.vs vec)) (Vec?.sz vec))

/// Capacity

unfold val size_of: #a:Type -> #st:eqtype -> vec:vector a st -> Tot st
unfold let size_of #a #st vec =
  Vec?.sz vec

unfold val capacity_of: #a:Type -> #st:eqtype -> vec:vector a st -> Tot st
unfold let capacity_of #a #st vec =
  Vec?.cap vec

unfold val is_empty: #a:Type -> #st:eqtype -> vec:vector a st -> Tot bool
unfold let is_empty #a #st vec =
  B.len_is_0 (Vec?.vs vec)

unfold val is_full: #a:Type -> #st:eqtype -> vstr:vector_str a st -> Tot bool
unfold let is_full #a #st vstr =
  B.size_is_max (Vec?.sz vstr)

/// Memory-related

unfold val live: #a:Type -> #st:eqtype -> HS.mem -> vector a st -> GTot Type0
unfold let live #a #st h vec =
  B.live h (Vec?.vs vec)

unfold val freeable: #a:Type -> #st:eqtype -> vector a st -> GTot Type0
unfold let freeable #a #st vec =
  B.freeable (Vec?.vs vec)

unfold val loc_vector: #a:Type -> #st:eqtype -> vector a st -> GTot B.loc
unfold let loc_vector #a #st vec =
  B.loc_buffer (Vec?.vs vec)

unfold val loc_addr_of_vector: #a:Type -> #st:eqtype -> vector a st -> GTot B.loc
unfold let loc_addr_of_vector #a #st vec =
  B.loc_addr_of_buffer (Vec?.vs vec)

val loc_vector_within:
  #a:Type -> #st:eqtype -> vec:vector a st ->
  i:st -> j:st{B.size_lte i j && B.size_lte j (size_of vec) } ->
  GTot B.loc (decreases ((B.size2nat j - B.size2nat i)))
// unfold let loc_vector_within #a vec i j =
//   B.loc_buffer (B.gsub (Vec?.vs vec) i (j - i))
let rec loc_vector_within #a #st vec i j =
  if i = j then B.loc_none
  else B.loc_union (B.loc_buffer (B.gsub (Vec?.vs vec) i (B.size_one (Vec?.vs vec))))
		 (loc_vector_within #a #st vec (B.size_inc i) j)

val loc_vector_within_includes_:
  #a:Type -> #st:eqtype -> vec:vector a st ->
  i:uint64_t ->
  j1:uint64_t{i <= j1 && j1 <= size_of vec} ->
  j2:uint64_t{i <= j2 && j2 <= j1} ->
  Lemma (requires True)
	(ensures (loc_includes (loc_vector_within vec i j1)
			       (loc_vector_within vec i j2)))
	(decreases (U64.v (j1 - i)))
let rec loc_vector_within_includes_ #a vec i j1 j2 =
  if i = j1 then ()
  else if i = j2 then ()
  else begin
    loc_vector_within_includes_ vec (i + 1UL) j1 j2;
    loc_includes_union_l (B.loc_buffer (B.gsub (Vec?.vs vec) i 1UL))
    			 (loc_vector_within vec (i + 1UL) j1)
    			 (loc_vector_within vec (i + 1UL) j2);
    loc_includes_union_r (loc_vector_within vec i j1)
			 (B.loc_buffer (B.gsub (Vec?.vs vec) i 1UL))
			 (loc_vector_within vec (i + 1UL) j2)
  end

val loc_vector_within_includes:
  #a:Type -> #st:eqtype -> vec:vector a st ->
  i1:uint64_t -> j1:uint64_t{i1 <= j1 && j1 <= size_of vec} ->
  i2:uint64_t{i1 <= i2} -> j2:uint64_t{i2 <= j2 && j2 <= j1} ->
  Lemma (requires True)
	(ensures (loc_includes (loc_vector_within vec i1 j1)
			       (loc_vector_within vec i2 j2)))
	(decreases (U64.v (j1 - i1)))
let rec loc_vector_within_includes #a vec i1 j1 i2 j2 =
  if i1 = j1 then ()
  else if i1 = i2 then loc_vector_within_includes_ vec i1 j1 j2
  else begin
    loc_vector_within_includes vec (i1 + 1UL) j1 i2 j2;
    loc_includes_union_l (B.loc_buffer (B.gsub (Vec?.vs vec) i1 1UL))
			 (loc_vector_within vec (i1 + 1UL) j1)
			 (loc_vector_within vec i2 j2)
  end

val loc_vector_within_included:
  #a:Type -> #st:eqtype -> vec:vector a st ->
  i:uint64_t -> j:uint64_t{i <= j && j <= size_of vec} ->
  Lemma (requires True)
	(ensures (loc_includes (loc_vector vec)
			       (loc_vector_within vec i j)))
	(decreases (U64.v (j - i)))
let rec loc_vector_within_included #a vec i j =
  if i = j then ()
  else loc_vector_within_included vec (i + 1UL) j

val loc_vector_within_disjoint_:
  #a:Type -> #st:eqtype -> vec:vector a st ->
  i1:uint64_t ->
  i2:uint64_t{i1 < i2} ->
  j2:uint64_t{i2 <= j2 && j2 <= size_of vec} ->
  Lemma (requires True)
	(ensures (loc_disjoint (B.loc_buffer (B.gsub (Vec?.vs vec) i1 1UL))
			       (loc_vector_within vec i2 j2)))
	(decreases (U64.v (j2 - i2)))
let rec loc_vector_within_disjoint_ #a vec i1 i2 j2 =
  if i2 = j2 then ()
  else loc_vector_within_disjoint_ vec i1 (i2 + 1UL) j2

val loc_vector_within_disjoint:
  #a:Type -> #st:eqtype -> vec:vector a st ->
  i1:uint64_t -> j1:uint64_t{i1 <= j1 && j1 <= size_of vec} ->
  i2:uint64_t{j1 <= i2} -> j2:uint64_t{i2 <= j2 && j2 <= size_of vec} ->
  Lemma (requires True)
	(ensures (loc_disjoint (loc_vector_within vec i1 j1)
			       (loc_vector_within vec i2 j2)))
	(decreases (U64.v (j1 - i1)))
let rec loc_vector_within_disjoint #a vec i1 j1 i2 j2 =
  if i1 = j1 then ()
  else (loc_vector_within_disjoint_ vec i1 i2 j2;
       loc_vector_within_disjoint vec (i1 + 1UL) j1 i2 j2)

val loc_vector_within_union_rev:
  #a:Type -> #st:eqtype -> vec:vector a st ->
  i:uint64_t -> j:uint64_t{i < j && j <= size_of vec} ->
  Lemma (requires True)
	(ensures (loc_vector_within vec i j ==
		 loc_union (loc_vector_within vec i (j - 1UL))
			   (loc_vector_within vec (j - 1UL) j)))
	(decreases (U64.v (j - i)))
let rec loc_vector_within_union_rev #a vec i j =
  if i = j - 1UL then ()
  else begin
    loc_vector_within_union_rev vec (i + 1UL) j;
    loc_union_assoc (B.loc_buffer (B.gsub (Vec?.vs vec) i 1UL))
		    (loc_vector_within vec (i + 1UL) (j - 1UL))
		    (loc_vector_within vec (j - 1UL) j)
  end

unfold val frameOf: #a:Type -> #st:eqtype -> vector a st -> Tot HH.rid
unfold let frameOf #a #st vec =
  B.frameOf (Vec?.vs vec)

unfold val hmap_dom_eq: h0:HS.mem -> h1:HS.mem -> GTot Type0
unfold let hmap_dom_eq h0 h1 =
  Set.equal (Map.domain (MHS.get_hmap h0))
	    (Map.domain (MHS.get_hmap h1))

val modifies_as_seq:
  #a:Type -> #st:eqtype -> vec:vector a st -> dloc:loc ->
  h0:HS.mem -> h1:HS.mem ->
  Lemma (requires (live h0 vec /\
		  loc_disjoint (loc_vector vec) dloc /\
		  modifies dloc h0 h1))
	(ensures (as_seq h0 vec == as_seq h1 vec))
	[SMTPat (live h0 vec);
	SMTPat (loc_disjoint (loc_vector vec) dloc);
	SMTPat (modifies dloc h0 h1)]
let modifies_as_seq #a vec dloc h0 h1 =
  B.modifies_buffer_elim (Vec?.vs vec) dloc h0 h1

val modifies_as_seq_within:
  #a:Type -> #st:eqtype -> vec:vector a st ->
  i:uint64_t -> j:uint64_t{i <= j && j <= size_of vec} ->
  dloc:loc -> h0:HS.mem -> h1:HS.mem ->
  Lemma (requires (live h0 vec /\
		  loc_disjoint (loc_vector_within vec i j) dloc /\
		  modifies dloc h0 h1))
	(ensures (S.slice (as_seq h0 vec) (U64.v i) (U64.v j) ==
		 S.slice (as_seq h1 vec) (U64.v i) (U64.v j)))
	(decreases (U64.v (j - i)))
	[SMTPat (live h0 vec);
	SMTPat (loc_disjoint (loc_vector_within vec i j) dloc);
	SMTPat (modifies dloc h0 h1)]
let rec modifies_as_seq_within #a vec i j dloc h0 h1 =
  if i = j then ()
  else begin
    B.modifies_buffer_elim (B.gsub (Vec?.vs vec) i 1UL) dloc h0 h1;
    modifies_as_seq_within vec (i + 1UL) j dloc h0 h1;
    assert (S.equal (S.slice (as_seq h0 vec) (U64.v i) (U64.v j))
		    (S.append (S.slice (as_seq h0 vec) (U64.v i) (U64.v i + 1))
			      (S.slice (as_seq h0 vec) (U64.v i + 1) (U64.v j))));
    assert (S.equal (S.slice (as_seq h1 vec) (U64.v i) (U64.v j))
		    (S.append (S.slice (as_seq h1 vec) (U64.v i) (U64.v i + 1))
			      (S.slice (as_seq h1 vec) (U64.v i + 1) (U64.v j))))
  end

/// Construction

val create_empty:
  a:Type -> Tot (vec:vector a{size_of vec = 0UL})
let create_empty a =
  Vec 0UL 0UL B.null

val create_empty_as_seq_empty:
  a:Type -> h:HS.mem ->
  Lemma (S.equal (as_seq h (create_empty a)) S.empty)
	[SMTPat (as_seq h (create_empty a))]
let create_empty_as_seq_empty a h = ()

val create_rid:
  #a:Type -> len:uint64_t{len > 0UL} -> v:a ->
  rid:HH.rid{HST.is_eternal_region rid} ->
  HST.ST (vector a)
	 (requires (fun h0 -> true))
	 (ensures (fun h0 vec h1 ->
	   frameOf vec = rid /\
	   live h1 vec /\ freeable vec /\
	   modifies loc_none h0 h1 /\
	   Set.equal (Map.domain (MHS.get_hmap h0))
                     (Map.domain (MHS.get_hmap h1)) /\
	   size_of vec = len /\
	   S.equal (as_seq h1 vec) (S.create (U64.v len) v)))
let create_rid #a len v rid =
  Vec len len (B.malloc rid v len)

val create:
  #a:Type -> len:uint64_t{len > 0UL} -> v:a ->
  HST.ST (vector a)
	 (requires (fun h0 -> true))
	 (ensures (fun h0 vec h1 ->
	   frameOf vec = HH.root /\
	   live h1 vec /\ freeable vec /\
	   modifies loc_none h0 h1 /\
	   Set.equal (Map.domain (MHS.get_hmap h0))
                     (Map.domain (MHS.get_hmap h1)) /\
	   size_of vec = len /\
	   S.equal (as_seq h1 vec) (S.create (U64.v len) v)))
let create #a len v =
  create_rid len v HH.root

val create_reserve:
  #a:Type -> len:uint64_t{len > 0UL} -> ia:a ->
  rid:HH.rid{HST.is_eternal_region rid} ->
  HST.ST (vector a)
	 (requires (fun h0 -> true))
	 (ensures (fun h0 vec h1 ->
	   frameOf vec = rid /\ live h1 vec /\ freeable vec /\
	   modifies loc_none h0 h1 /\
	   Set.equal (Map.domain (MHS.get_hmap h0))
                     (Map.domain (MHS.get_hmap h1)) /\
	   size_of vec = 0UL /\
	   S.equal (as_seq h1 vec) S.empty))
let create_reserve #a len ia rid =
  Vec 0UL len (B.malloc rid ia len)

val create_by_buffer:
  #a:Type -> len:uint64_t{len > 0UL} ->
  buf:B.buffer a{B.len buf = len} ->
  HST.ST (vector a)
	 (requires (fun h0 -> B.live h0 buf))
	 (ensures (fun h0 vec h1 ->
	   frameOf vec = B.frameOf buf /\ loc_vector vec == B.loc_buffer buf /\
	   live h1 vec /\ h0 == h1 /\
	   size_of vec = len /\
	   S.equal (as_seq h1 vec) (B.as_seq h0 buf)))
let create_by_buffer #a len buf =
  Vec len len buf

/// Destruction

val free:
  #a:Type -> #st:eqtype -> vec:vector a st ->
  HST.ST unit
    (requires (fun h0 -> live h0 vec /\ freeable vec))
    (ensures (fun h0 _ h1 -> modifies (loc_addr_of_vector vec) h0 h1))
let free #a #st vec =
  B.free (Vec?.vs vec)

/// Element access

val get:
  #a:Type -> h:HS.mem -> vec:vector a st ->
  i:uint64_t{i < size_of vec} -> GTot a
let get #a h vec i =
  S.index (as_seq h vec) (U64.v i)

val index:
  #a:Type -> #st:eqtype -> vec:vector a st -> i:uint64_t ->
  HST.ST a
    (requires (fun h0 -> live h0 vec /\ i < size_of vec))
    (ensures (fun h0 v h1 ->
      h0 == h1 /\ S.index (as_seq h1 vec) (U64.v i) == v))
let index #a vec i =
  B.index (Vec?.vs vec) i

val front:
  #a:Type -> #st:eqtype -> vec:vector a{size_of vec > 0UL} ->
  HST.ST a
    (requires (fun h0 -> live h0 vec))
    (ensures (fun h0 v h1 ->
      h0 == h1 /\ S.index (as_seq h1 vec) 0 == v))
let front #a #st vec =
  B.index (Vec?.vs vec) 0UL

val back:
  #a:Type -> #st:eqtype -> vec:vector a{size_of vec > 0UL} ->
  HST.ST a
    (requires (fun h0 -> live h0 vec))
    (ensures (fun h0 v h1 ->
      h0 == h1 /\ S.index (as_seq h1 vec) (U64.v (size_of vec) - 1) == v))
let back #a #st vec =
  B.index (Vec?.vs vec) (size_of vec - 1UL)

/// Operations

val clear:
  #a:Type -> #st:eqtype -> vec:vector a st ->
  Tot (cvec:vector a{size_of cvec = 0UL})
let clear #a #st vec =
  Vec 0UL (Vec?.cap vec) (Vec?.vs vec)

val clear_as_seq_empty:
  #a:Type -> h:HS.mem -> vec:vector a st ->
  Lemma (S.equal (as_seq h (clear vec)) S.empty)
	[SMTPat (as_seq h (clear vec))]
let clear_as_seq_empty #a h vec = ()

private val slice_append:
  #a:Type -> s:S.seq a ->
  i:nat -> j:nat{i <= j} -> k:nat{j <= k && k <= S.length s} ->
  Lemma (S.equal (S.slice s i k)
		 (S.append (S.slice s i j) (S.slice s j k)))
private let slice_append #a s i j k = ()

val assign:
  #a:Type -> #st:eqtype -> vec:vector a st ->
  i:uint64_t -> v:a ->
  HST.ST unit
    (requires (fun h0 -> live h0 vec /\ i < size_of vec))
    (ensures (fun h0 _ h1 ->
      hmap_dom_eq h0 h1 /\
      modifies (loc_vector_within #a vec i (i + 1UL)) h0 h1 /\
      get h1 vec i == v /\
      S.equal (as_seq h1 vec) (S.upd (as_seq h0 vec) (U64.v i) v)))
#reset-options "--z3rlimit 10"
let assign #a vec i v =
  let hh0 = HST.get () in
  // NOTE: `B.upd (Vec?.vs vec) i v` makes more sense,
  //       but the `modifies` postcondition is coarse-grained.
  B.upd (B.sub (Vec?.vs vec) i 1UL) 0UL v;
  let hh1 = HST.get () in
  loc_vector_within_disjoint vec 0UL i i (i + 1UL);
  modifies_as_seq_within
    vec 0UL i (loc_vector_within #a vec i (i + 1UL)) hh0 hh1;
  loc_vector_within_disjoint vec i (i + 1UL) (i + 1UL) (size_of vec);
  modifies_as_seq_within
    vec (i + 1UL) (size_of vec) (loc_vector_within #a vec i (i + 1UL)) hh0 hh1;
  slice_append (as_seq hh1 vec) 0 (U64.v i) (U64.v i + 1);
  slice_append (as_seq hh1 vec) 0 (U64.v i + 1) (U64.v (size_of vec));
  slice_append (S.upd (as_seq hh0 vec) (U64.v i) v) 0 (U64.v i) (U64.v i + 1);
  slice_append (S.upd (as_seq hh0 vec) (U64.v i) v) 0 (U64.v i + 1) (U64.v (size_of vec))

private val resize_ratio: uint64_t
private let resize_ratio = 2UL

private val new_capacity: cap:uint64_t{cap > 0UL} -> Tot uint64_t
private let new_capacity cap =
  if cap >= max_uint64 / resize_ratio then max_uint64
  else cap * resize_ratio

val insert:
  #a:Type -> #st:eqtype -> vec:vector a st -> v:a ->
  HST.ST (vector a)
    (requires (fun h0 ->
      live h0 vec /\ freeable vec /\ not (is_full vec) /\
      HST.is_eternal_region (frameOf vec)))
    (ensures (fun h0 nvec h1 ->
      frameOf vec = frameOf nvec /\
      hmap_dom_eq h0 h1 /\
      live h1 nvec /\ freeable nvec /\
      modifies (loc_union (loc_addr_of_vector vec)
      			  (loc_vector nvec)) h0 h1 /\
      size_of nvec = size_of vec + 1UL /\
      get h1 nvec (size_of vec) == v /\
      S.equal (as_seq h1 nvec) (S.snoc (as_seq h0 vec) v)))
#reset-options "--z3rlimit 20"
let insert #a vec v =
  let sz = Vec?.sz vec in
  let cap = Vec?.cap vec in
  let vs = Vec?.vs vec in
  if sz = cap
  then (let ncap = new_capacity cap in
       let nvs = B.malloc (B.frameOf vs) v ncap in
       B.blit vs 0UL nvs 0UL sz;
       B.upd nvs sz v;
       B.free vs;
       Vec (sz + 1UL) ncap nvs)
  else
    (B.upd vs sz v;
    Vec (sz + 1UL) cap vs)

val flush:
  #a:Type -> #st:eqtype -> vec:vector a st -> ia:a ->
  i:uint64_t{i <= size_of vec} ->
  HST.ST (vector a)
    (requires (fun h0 ->
      live h0 vec /\ freeable vec /\
      HST.is_eternal_region (frameOf vec)))
    (ensures (fun h0 fvec h1 ->
      frameOf vec = frameOf fvec /\
      hmap_dom_eq h0 h1 /\
      live h1 fvec /\ freeable fvec /\
      modifies (loc_union (loc_addr_of_vector vec)
      			  (loc_vector fvec)) h0 h1 /\
      size_of fvec = size_of vec - i /\
      S.equal (as_seq h1 fvec)
	      (S.slice (as_seq h0 vec) (U64.v i) (U64.v (size_of vec)))))
let flush #a vec ia i =
  let fsz = Vec?.sz vec - i in
  let asz = if Vec?.sz vec = i then 1UL else fsz in
  let vs = Vec?.vs vec in
  let fvs = B.malloc (B.frameOf vs) ia asz in
  B.blit vs i fvs 0UL fsz;
  B.free vs;
  Vec fsz asz fvs

/// Iteration

val fold_left_seq:
  #a:Type -> #b:Type0 -> seq:S.seq a ->
  f:(b -> a -> GTot b) -> ib:b ->
  GTot b (decreases (S.length seq))
let rec fold_left_seq #a #b seq f ib =
  if S.length seq = 0 then ib
  else fold_left_seq (S.tail seq) f (f ib (S.head seq))

val fold_left_buffer:
  #a:Type -> #b:Type0 -> len:uint64_t ->
  buf:B.buffer a{B.len buf = len} ->
  f:(b -> a -> Tot b) -> ib:b ->
  HST.ST b
    (requires (fun h0 -> B.live h0 buf))
    (ensures (fun h0 v h1 ->
      h0 == h1 /\
      v == fold_left_seq (B.as_seq h0 buf) f ib))
    (decreases (B.length buf))
let rec fold_left_buffer #a #b len buf f ib =
  if len = 0UL then ib
  else (fold_left_buffer (len - 1UL) (B.sub buf 1UL (len - 1UL))
			 f (f ib (B.index buf 0UL)))

val fold_left:
  #a:Type -> #b:Type0 -> vec:vector a st ->
  f:(b -> a -> Tot b) -> ib:b ->
  HST.ST b
    (requires (fun h0 -> live h0 vec))
    (ensures (fun h0 v h1 ->
      h0 == h1 /\
      v == fold_left_seq (as_seq h0 vec) f ib))
let fold_left #a #b vec f ib =
  fold_left_buffer (Vec?.sz vec) (B.sub (Vec?.vs vec) 0UL (Vec?.sz vec)) f ib

val forall_seq:
  #a:Type -> seq:S.seq a ->
  i:nat -> j:nat{i <= j && j <= S.length seq} ->
  p:(a -> GTot Type0) -> GTot Type0
let forall_seq #a seq i j p =
  forall (idx:nat{i <= idx && idx < j}).
    p (S.index seq idx)

val forall_buffer:
  #a:Type -> h:HS.mem -> buf:B.buffer a ->
  i:nat -> j:nat{i <= j && j <= B.length buf} ->
  p:(a -> GTot Type0) -> GTot Type0
let forall_buffer #a h buf i j p =
  forall_seq (B.as_seq h buf) i j p

val forall_:
  #a:Type -> h:HS.mem -> vec:vector a st ->
  i:uint64_t -> j:uint64_t{i <= j && j <= size_of vec} ->
  p:(a -> Tot Type0) -> GTot Type0
let forall_ #a h vec i j p =
  forall_seq (as_seq h vec) (U64.v i) (U64.v j) p

val forall_all:
  #a:Type -> h:HS.mem -> vec:vector a st ->
  p:(a -> Tot Type0) -> GTot Type0
let forall_all #a h vec p =
  forall_ h vec 0UL (size_of vec) p

val forall2_seq:
  #a:Type -> seq:S.seq a ->
  i:nat -> j:nat{i <= j && j <= S.length seq} ->
  p:(a -> a -> GTot Type0) -> GTot Type0
let forall2_seq #a seq i j p =
  forall (k:nat{i <= k && k < j}) (l:nat{i <= l && l < j && k <> l}).
    p (S.index seq k) (S.index seq l)

val forall2_buffer:
  #a:Type -> h:HS.mem -> buf:B.buffer a ->
  i:nat -> j:nat{i <= j && j <= B.length buf} ->
  p:(a -> a -> GTot Type0) -> GTot Type0
let forall2_buffer #a h buf i j p =
  forall2_seq (B.as_seq h buf) i j p

val forall2:
  #a:Type -> h:HS.mem -> vec:vector a st ->
  i:uint64_t -> j:uint64_t{i <= j && j <= size_of vec} ->
  p:(a -> a -> GTot Type0) -> GTot Type0
let forall2 #a h vec i j p =
  forall2_seq (as_seq h vec) (U64.v i) (U64.v j) p

val forall2_all:
  #a:Type -> h:HS.mem -> vec:vector a st ->
  p:(a -> a -> GTot Type0) -> GTot Type0
let forall2_all #a h vec p =
  forall2 h vec 0UL (size_of vec) p

(*! Facts *)

val forall_seq_ok:
  #a:Type -> seq:S.seq a ->
  i:nat -> j:nat{i <= j && j <= S.length seq} ->
  k:nat{i <= k && k < j} ->
  p:(a -> GTot Type0) ->
  Lemma (requires (forall_seq seq i j p))
	(ensures (p (S.index seq k)))
let forall_seq_ok #a seq i j k p = ()

val forall2_seq_ok:
  #a:Type -> seq:S.seq a ->
  i:nat -> j:nat{i <= j && j <= S.length seq} ->
  k:nat{i <= k && k < j} -> l:nat{i <= l && l < j && k <> l} ->
  p:(a -> a -> GTot Type0) ->
  Lemma (requires (forall2_seq seq i j p))
	(ensures (p (S.index seq k) (S.index seq l)))
let forall2_seq_ok #a seq i j k l p = ()

val get_as_seq_index:
  #a:Type -> h:HS.mem -> buf:B.buffer a -> i:uint64_t{i < B.len buf} ->
  Lemma (B.get h buf (U64.v i) == S.index (B.as_seq h (B.gsub buf i 1UL)) 0)
let get_as_seq_index #a h buf i = ()

val get_preserved:
  #a:Type -> #st:eqtype -> vec:vector a st ->
  i:uint64_t{i < size_of vec} ->
  p:loc -> h0:HS.mem -> h1:HS.mem ->
  Lemma (requires (live h0 vec /\
		  loc_disjoint p (loc_vector_within vec i (i + 1UL)) /\
		  modifies p h0 h1))
	(ensures (get h0 vec i == get h1 vec i))
let get_preserved #a vec i p h0 h1 =
  get_as_seq_index h0 (Vec?.vs vec) i;
  get_as_seq_index h1 (Vec?.vs vec) i

private val get_preserved_within:
  #a:Type -> #st:eqtype -> vec:vector a st ->
  i:uint64_t -> j:uint64_t{i <= j && j <= size_of vec} ->
  k:uint64_t{(k < i || j <= k) && k < size_of vec} ->
  h0:HS.mem -> h1:HS.mem ->
  Lemma (requires (live h0 vec /\
		  modifies (loc_vector_within vec i j) h0 h1))
	(ensures (get h0 vec k == get h1 vec k))
	[SMTPat (live h0 vec);
	SMTPat (modifies (loc_vector_within vec i j) h0 h1);
	SMTPat (get h0 vec k)]
let rec get_preserved_within #a vec i j k h0 h1 =
  if k < i then begin
    loc_vector_within_disjoint vec k (k + 1UL) i j;
    get_preserved vec k (loc_vector_within vec i j) h0 h1
  end
  else begin
    loc_vector_within_disjoint vec i j k (k + 1UL);
    get_preserved vec k (loc_vector_within vec i j) h0 h1
  end

val forall_as_seq:
  #a:Type -> s0:S.seq a -> s1:S.seq a{S.length s0 = S.length s1} ->
  i:nat -> j:nat{i <= j && j <= S.length s0} ->
  k:nat{i <= k && k < j} ->
  p:(a -> Tot Type0) ->
  Lemma (requires (p (S.index s0 k) /\ S.slice s0 i j == S.slice s1 i j))
	(ensures (p (S.index s1 k)))
	[SMTPat (p (S.index s0 k));
	SMTPat (S.slice s0 i j == S.slice s1 i j)]
let forall_as_seq #a s0 s1 i j k p =
  assert (S.index (S.slice s0 i j) (k - i) ==
	 S.index (S.slice s1 i j) (k - i))

val forall_preserved:
  #a:Type -> #st:eqtype -> vec:vector a st ->
  i:uint64_t -> j:uint64_t{i <= j && j <= size_of vec} ->
  p:(a -> Tot Type0) ->
  dloc:loc -> h0:HS.mem -> h1:HS.mem ->
  Lemma (requires (live h0 vec /\
		  loc_disjoint (loc_vector_within vec i j) dloc /\
		  forall_ h0 vec i j p /\
		  modifies dloc h0 h1))
	(ensures (forall_ h1 vec i j p))
let forall_preserved #a vec i j p dloc h0 h1 =
  modifies_as_seq_within vec i j dloc h0 h1;
  assert (S.slice (as_seq h0 vec) (U64.v i) (U64.v j) ==
	 S.slice (as_seq h1 vec) (U64.v i) (U64.v j))

val forall2_extend:
  #a:Type -> h:HS.mem -> vec:vector a st ->
  i:uint64_t -> j:uint64_t{i <= j && j < size_of vec} ->
  p:(a -> a -> Tot Type0) ->
  Lemma (requires (forall2 h vec i j p /\
		  forall_ h vec i j
		    (fun a -> p a (get h vec j) /\ p (get h vec j) a)))
	(ensures (forall2 h vec i (j + 1UL) p))
let forall2_extend #a h vec i j p = ()

val forall2_forall_left:
  #a:Type -> h:HS.mem -> vec:vector a st ->
  i:uint64_t -> j:uint64_t{i <= j && j <= size_of vec} ->
  k:uint64_t{i <= k && k < j} ->
  p:(a -> a -> Tot Type0) ->
  Lemma (requires (forall2 h vec i j p))
	(ensures (forall_ h vec i k (p (get h vec k))))
let forall2_forall_left #a h vec i j k p = ()

val forall2_forall_right:
  #a:Type -> h:HS.mem -> vec:vector a st ->
  i:uint64_t -> j:uint64_t{i <= j && j <= size_of vec} ->
  k:uint64_t{i <= k && k < j} ->
  p:(a -> a -> Tot Type0) ->
  Lemma (requires (forall2 h vec i j p))
	(ensures (forall_ h vec (k + 1UL) j (p (get h vec k))))
let forall2_forall_right #a h vec i j k p = ()

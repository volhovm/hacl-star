module Low.Vector64

open FStar.All
open FStar.Integers
open LowStar.Modifies

module HH = FStar.Monotonic.HyperHeap
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module MHS = FStar.Monotonic.HyperStack
module S = FStar.Seq

type size_t = UInt64.t
type index_t = size_t

let max_size: size_t = 18446744073709551615UL
let sz0: size_t = 0UL
let sz1: size_t = 1UL
let index2nat (x:index_t): nat = UInt64.v x

module SZMOD = FStar.UInt64
module SZBUF = LowStar.Buffer64

let modifies = SZBUF.modifies
let loc = SZBUF.loc
let loc_none = SZBUF.loc_none
let loc_buffer #a #rrel #rel = SZBUF.loc_buffer #a #rrel #rel
let loc_union = SZBUF.loc_union
let loc_disjoint = SZBUF.loc_disjoint
let loc_includes = SZBUF.loc_includes

/// Abstract vector type

noeq type vector_str a =
| Vec: sz:size_t ->
       cap:size_t{cap >= sz} ->
       vs:SZBUF.buffer a{SZBUF.len vs = cap} -> 
       vector_str a

val vector (a: Type0): Tot Type0
let vector a = vector_str a

/// Specification

val as_seq: 
  HS.mem -> #a:Type -> vec:vector a -> 
  GTot (s:S.seq a{S.length s = SZMOD.v (Vec?.sz vec)})
let as_seq h #a vec =
  SZBUF.as_seq h (SZBUF.gsub (Vec?.vs vec) sz0 (Vec?.sz vec))

/// Capacity

unfold val size_of: #a:Type -> vec:vector a -> Tot size_t
unfold let size_of #a vec = 
  Vec?.sz vec

unfold val capacity_of: #a:Type -> vec:vector a -> Tot size_t
unfold let capacity_of #a vec =
  Vec?.cap vec

unfold val is_empty: #a:Type -> vec:vector a -> Tot bool
unfold let is_empty #a vec =
  size_of vec = sz0

unfold val is_full: #a:Type -> vstr:vector_str a -> GTot bool
unfold let is_full #a vstr =
  Vec?.sz vstr >= max_size

/// Memory-related

unfold val live: #a:Type -> HS.mem -> vector a -> GTot Type0
unfold let live #a h vec =
  SZBUF.live h (Vec?.vs vec)

unfold val freeable: #a:Type -> vector a -> GTot Type0
unfold let freeable #a vec =
  SZBUF.freeable (Vec?.vs vec)

unfold val loc_vector: #a:Type -> vector a -> GTot loc
unfold let loc_vector #a vec =
  loc_buffer (Vec?.vs vec)

unfold val loc_addr_of_vector: #a:Type -> vector a -> GTot loc
unfold let loc_addr_of_vector #a vec =
  SZBUF.loc_addr_of_buffer (Vec?.vs vec)

val loc_vector_within:
  #a:Type -> vec:vector a -> 
  i:index_t -> j:index_t{i <= j && j <= size_of vec} -> 
  GTot loc (decreases (SZMOD.v (j - i)))
// unfold let loc_vector_within #a vec i j =
//   loc_buffer (SZBUF.gsub (Vec?.vs vec) i (j - i))
let rec loc_vector_within #a vec i j =
  if i = j then loc_none
  else loc_union (loc_buffer (SZBUF.gsub (Vec?.vs vec) i sz1))
		 (loc_vector_within vec (i + sz1) j)

val loc_vector_within_includes_:
  #a:Type -> vec:vector a -> 
  i:index_t -> 
  j1:index_t{i <= j1 && j1 <= size_of vec} -> 
  j2:index_t{i <= j2 && j2 <= j1} ->
  Lemma (requires True)
	(ensures (loc_includes (loc_vector_within vec i j1)
			       (loc_vector_within vec i j2)))
	(decreases (SZMOD.v (j1 - i)))
let rec loc_vector_within_includes_ #a vec i j1 j2 =
  if i = j1 then ()
  else if i = j2 then ()
  else begin
    loc_vector_within_includes_ vec (i + sz1) j1 j2;
    SZBUF.loc_includes_union_l (loc_buffer (SZBUF.gsub (Vec?.vs vec) i sz1))
    			 (loc_vector_within vec (i + sz1) j1)
    			 (loc_vector_within vec (i + sz1) j2);
    SZBUF.loc_includes_union_r (loc_vector_within vec i j1)
			 (loc_buffer (SZBUF.gsub (Vec?.vs vec) i sz1))
			 (loc_vector_within vec (i + sz1) j2)
  end

val loc_vector_within_includes:
  #a:Type -> vec:vector a -> 
  i1:index_t -> j1:index_t{i1 <= j1 && j1 <= size_of vec} -> 
  i2:index_t{i1 <= i2} -> j2:index_t{i2 <= j2 && j2 <= j1} ->
  Lemma (requires True)
	(ensures (loc_includes (loc_vector_within vec i1 j1)
			       (loc_vector_within vec i2 j2)))
	(decreases (SZMOD.v (j1 - i1)))
let rec loc_vector_within_includes #a vec i1 j1 i2 j2 =
  if i1 = j1 then ()
  else if i1 = i2 then loc_vector_within_includes_ vec i1 j1 j2
  else begin
    loc_vector_within_includes vec (i1 + sz1) j1 i2 j2;
    SZBUF.loc_includes_union_l (loc_buffer (SZBUF.gsub (Vec?.vs vec) i1 sz1))
			 (loc_vector_within vec (i1 + sz1) j1)
			 (loc_vector_within vec i2 j2)
  end

val loc_vector_within_included:
  #a:Type -> vec:vector a -> 
  i:index_t -> j:index_t{i <= j && j <= size_of vec} ->
  Lemma (requires True)
	(ensures (loc_includes (loc_vector vec)
			       (loc_vector_within vec i j)))
	(decreases (SZMOD.v (j - i)))
let rec loc_vector_within_included #a vec i j =
  if i = j then ()
  else loc_vector_within_included vec (i + sz1) j

val loc_vector_within_disjoint_:
  #a:Type -> vec:vector a -> 
  i1:index_t -> 
  i2:index_t{i1 < i2} ->
  j2:index_t{i2 <= j2 && j2 <= size_of vec} ->
  Lemma (requires True)
	(ensures (loc_disjoint (loc_buffer (SZBUF.gsub (Vec?.vs vec) i1 sz1))
			       (loc_vector_within vec i2 j2)))
	(decreases (SZMOD.v (j2 - i2)))
let rec loc_vector_within_disjoint_ #a vec i1 i2 j2 =
  if i2 = j2 then ()
  else loc_vector_within_disjoint_ vec i1 (i2 + sz1) j2

val loc_vector_within_disjoint:
  #a:Type -> vec:vector a -> 
  i1:index_t -> j1:index_t{i1 <= j1 && j1 <= size_of vec} -> 
  i2:index_t{j1 <= i2} -> j2:index_t{i2 <= j2 && j2 <= size_of vec} ->
  Lemma (requires True)
	(ensures (loc_disjoint (loc_vector_within vec i1 j1)
			       (loc_vector_within vec i2 j2)))
	(decreases (SZMOD.v (j1 - i1)))
let rec loc_vector_within_disjoint #a vec i1 j1 i2 j2 =
  if i1 = j1 then ()
  else (loc_vector_within_disjoint_ vec i1 i2 j2;
       loc_vector_within_disjoint vec (i1 + sz1) j1 i2 j2)

val loc_vector_within_union_rev:
  #a:Type -> vec:vector a -> 
  i:index_t -> j:index_t{i < j && j <= size_of vec} ->
  Lemma (requires True)
	(ensures (loc_vector_within vec i j ==
		 loc_union (loc_vector_within vec i (j - sz1))
			   (loc_vector_within vec (j - sz1) j)))
	(decreases (SZMOD.v (j - i)))
let rec loc_vector_within_union_rev #a vec i j =
  if i = j - sz1 then ()
  else begin
    loc_vector_within_union_rev vec (i + sz1) j;
    SZBUF.loc_union_assoc (loc_buffer (SZBUF.gsub (Vec?.vs vec) i sz1))
		    (loc_vector_within vec (i + sz1) (j - sz1))
		    (loc_vector_within vec (j - sz1) j)
  end

unfold val frameOf: #a:Type -> vector a -> Tot HH.rid
unfold let frameOf #a vec =
  SZBUF.frameOf (Vec?.vs vec)

unfold val hmap_dom_eq: h0:HS.mem -> h1:HS.mem -> GTot Type0
unfold let hmap_dom_eq h0 h1 =
  Set.equal (Map.domain (MHS.get_hmap h0))
	    (Map.domain (MHS.get_hmap h1))

val modifies_as_seq:
  #a:Type -> vec:vector a -> dloc:loc ->
  h0:HS.mem -> h1:HS.mem ->
  Lemma (requires (live h0 vec /\ 
		  loc_disjoint (loc_vector vec) dloc /\
		  modifies dloc h0 h1))
	(ensures (as_seq h0 vec == as_seq h1 vec))
	[SMTPat (live h0 vec); 
	SMTPat (loc_disjoint (loc_vector vec) dloc);
	SMTPat (modifies dloc h0 h1)]
let modifies_as_seq #a vec dloc h0 h1 =
  SZBUF.modifies_buffer_elim (Vec?.vs vec) dloc h0 h1

val modifies_as_seq_within:
  #a:Type -> vec:vector a -> 
  i:index_t -> j:index_t{i <= j && j <= size_of vec} ->
  dloc:loc -> h0:HS.mem -> h1:HS.mem ->
  Lemma (requires (live h0 vec /\ 
		  loc_disjoint (loc_vector_within vec i j) dloc /\
		  modifies dloc h0 h1))
	(ensures (S.slice (as_seq h0 vec) (SZMOD.v i) (SZMOD.v j) == 
		 S.slice (as_seq h1 vec) (SZMOD.v i) (SZMOD.v j)))
	(decreases (SZMOD.v (j - i)))
	[SMTPat (live h0 vec); 
	SMTPat (loc_disjoint (loc_vector_within vec i j) dloc);
	SMTPat (modifies dloc h0 h1)]
let rec modifies_as_seq_within #a vec i j dloc h0 h1 =
  if i = j then ()
  else begin
    SZBUF.modifies_buffer_elim (SZBUF.gsub (Vec?.vs vec) i sz1) dloc h0 h1;
    modifies_as_seq_within vec (i + sz1) j dloc h0 h1;
    assert (S.equal (S.slice (as_seq h0 vec) (SZMOD.v i) (SZMOD.v j))
		    (S.append (S.slice (as_seq h0 vec) (SZMOD.v i) (SZMOD.v i + 1))
			      (S.slice (as_seq h0 vec) (SZMOD.v i + 1) (SZMOD.v j))));
    assert (S.equal (S.slice (as_seq h1 vec) (SZMOD.v i) (SZMOD.v j))
		    (S.append (S.slice (as_seq h1 vec) (SZMOD.v i) (SZMOD.v i + 1))
			      (S.slice (as_seq h1 vec) (SZMOD.v i + 1) (SZMOD.v j))))
  end

/// Construction

val create_empty: 
  a:Type -> Tot (vec:vector a{size_of vec = sz0})
let create_empty a =
  Vec sz0 sz0 SZBUF.null

val create_empty_as_seq_empty:
  a:Type -> h:HS.mem ->
  Lemma (S.equal (as_seq h (create_empty a)) S.empty)
	[SMTPat (as_seq h (create_empty a))]
let create_empty_as_seq_empty a h = ()

val create_rid:
  #a:Type -> len:size_t{len > sz0} -> v:a ->
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
	   S.equal (as_seq h1 vec) (S.create (SZMOD.v len) v)))
let create_rid #a len v rid =
  Vec len len (SZBUF.malloc rid v len)

val create: 
  #a:Type -> len:size_t{len > sz0} -> v:a -> 
  HST.ST (vector a)
	 (requires (fun h0 -> true))
	 (ensures (fun h0 vec h1 -> 
	   frameOf vec = HH.root /\
	   live h1 vec /\ freeable vec /\
	   modifies loc_none h0 h1 /\
	   Set.equal (Map.domain (MHS.get_hmap h0))
                     (Map.domain (MHS.get_hmap h1)) /\
	   size_of vec = len /\
	   S.equal (as_seq h1 vec) (S.create (SZMOD.v len) v)))
let create #a len v =
  create_rid len v HH.root

val create_reserve:
  #a:Type -> len:size_t{len > sz0} -> ia:a ->
  rid:HH.rid{HST.is_eternal_region rid} ->
  HST.ST (vector a)
	 (requires (fun h0 -> true))
	 (ensures (fun h0 vec h1 -> 
	   frameOf vec = rid /\ live h1 vec /\ freeable vec /\
	   modifies loc_none h0 h1 /\
	   Set.equal (Map.domain (MHS.get_hmap h0))
                     (Map.domain (MHS.get_hmap h1)) /\
	   size_of vec = sz0 /\
	   S.equal (as_seq h1 vec) S.empty))
let create_reserve #a len ia rid =
  Vec sz0 len (SZBUF.malloc rid ia len)

val create_by_buffer:
  #a:Type -> len:size_t{len > sz0} ->
  buf:SZBUF.buffer a{SZBUF.len buf = len} ->
  HST.ST (vector a)
	 (requires (fun h0 -> SZBUF.live h0 buf))
	 (ensures (fun h0 vec h1 -> 
	   frameOf vec = SZBUF.frameOf buf /\ loc_vector vec == loc_buffer buf /\
	   live h1 vec /\ h0 == h1 /\
	   size_of vec = len /\
	   S.equal (as_seq h1 vec) (SZBUF.as_seq h0 buf)))
let create_by_buffer #a len buf =
  Vec len len buf

/// Destruction

val free:
  #a:Type -> vec:vector a ->
  HST.ST unit
    (requires (fun h0 -> live h0 vec /\ freeable vec))
    (ensures (fun h0 _ h1 -> modifies (loc_addr_of_vector vec) h0 h1))
let free #a vec =  
  SZBUF.free (Vec?.vs vec)

/// Element access

val get:
  #a:Type -> h:HS.mem -> vec:vector a -> 
  i:index_t{i < size_of vec} -> GTot a
let get #a h vec i =
  S.index (as_seq h vec) (SZMOD.v i)

val index: 
  #a:Type -> vec:vector a -> i:index_t -> 
  HST.ST a
    (requires (fun h0 -> live h0 vec /\ i < size_of vec))
    (ensures (fun h0 v h1 -> 
      h0 == h1 /\ S.index (as_seq h1 vec) (SZMOD.v i) == v))
let index #a vec i =
  SZBUF.index (Vec?.vs vec) i

val front:
  #a:Type -> vec:vector a{size_of vec > sz0} ->
  HST.ST a
    (requires (fun h0 -> live h0 vec))
    (ensures (fun h0 v h1 -> 
      h0 == h1 /\ S.index (as_seq h1 vec) 0 == v))
let front #a vec =
  SZBUF.index (Vec?.vs vec) sz0

val back:
  #a:Type -> vec:vector a{size_of vec > sz0} ->
  HST.ST a
    (requires (fun h0 -> live h0 vec))
    (ensures (fun h0 v h1 -> 
      h0 == h1 /\ S.index (as_seq h1 vec) (SZMOD.v (size_of vec) - 1) == v))
let back #a vec =
  SZBUF.index (Vec?.vs vec) (size_of vec - sz1)

/// Operations

val clear:
  #a:Type -> vec:vector a ->
  Tot (cvec:vector a{size_of cvec = sz0})
let clear #a vec =
  Vec sz0 (Vec?.cap vec) (Vec?.vs vec)

val clear_as_seq_empty:
  #a:Type -> h:HS.mem -> vec:vector a ->
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
  #a:Type -> vec:vector a ->
  i:index_t -> v:a ->
  HST.ST unit
    (requires (fun h0 -> live h0 vec /\ i < size_of vec))
    (ensures (fun h0 _ h1 ->
      hmap_dom_eq h0 h1 /\
      modifies (loc_vector_within #a vec i (i + sz1)) h0 h1 /\
      get h1 vec i == v /\
      S.equal (as_seq h1 vec) (S.upd (as_seq h0 vec) (SZMOD.v i) v)))
#reset-options "--z3rlimit 10"
let assign #a vec i v =
  let hh0 = HST.get () in
  // NOTE: `SZBUF.upd (Vec?.vs vec) i v` makes more sense, 
  //       but the `modifies` postcondition is coarse-grained.
  SZBUF.upd (SZBUF.sub (Vec?.vs vec) i sz1) sz0 v;
  let hh1 = HST.get () in
  loc_vector_within_disjoint vec sz0 i i (i + sz1);
  modifies_as_seq_within 
    vec sz0 i (loc_vector_within #a vec i (i + sz1)) hh0 hh1;
  loc_vector_within_disjoint vec i (i + sz1) (i + sz1) (size_of vec);
  modifies_as_seq_within 
    vec (i + sz1) (size_of vec) (loc_vector_within #a vec i (i + sz1)) hh0 hh1;
  slice_append (as_seq hh1 vec) 0 (SZMOD.v i) (SZMOD.v i + 1);
  slice_append (as_seq hh1 vec) 0 (SZMOD.v i + 1) (SZMOD.v (size_of vec));
  slice_append (S.upd (as_seq hh0 vec) (SZMOD.v i) v) 0 (SZMOD.v i) (SZMOD.v i + 1);
  slice_append (S.upd (as_seq hh0 vec) (SZMOD.v i) v) 0 (SZMOD.v i + 1) (SZMOD.v (size_of vec))

private val resize_ratio: size_t
private let resize_ratio = 2UL

private val new_capacity: cap:size_t{cap > sz0} -> Tot size_t
private let new_capacity cap =
  if cap >= max_size / resize_ratio then max_size
  else cap * resize_ratio

val insert: 
  #a:Type -> vec:vector a -> v:a -> 
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
      size_of nvec = size_of vec + sz1 /\
      get h1 nvec (size_of vec) == v /\
      S.equal (as_seq h1 nvec) (S.snoc (as_seq h0 vec) v)))
#reset-options "--z3rlimit 20"
let insert #a vec v =
  let sz = Vec?.sz vec in
  let cap = Vec?.cap vec in
  let vs = Vec?.vs vec in
  if sz = cap 
  then (let ncap = new_capacity cap in
       let nvs = SZBUF.malloc (SZBUF.frameOf vs) v ncap in
       SZBUF.blit vs sz0 nvs sz0 sz;
       SZBUF.upd nvs sz v;
       SZBUF.free vs;
       Vec (sz + sz1) ncap nvs)
  else
    (SZBUF.upd vs sz v;
    Vec (sz + sz1) cap vs)

val flush:
  #a:Type -> vec:vector a -> ia:a ->
  i:index_t{i <= size_of vec} ->
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
	      (S.slice (as_seq h0 vec) (SZMOD.v i) (SZMOD.v (size_of vec)))))
let flush #a vec ia i =
  let fsz = Vec?.sz vec - i in
  let asz = if Vec?.sz vec = i then sz1 else fsz in
  let vs = Vec?.vs vec in
  let fvs = SZBUF.malloc (SZBUF.frameOf vs) ia asz in
  SZBUF.blit vs i fvs sz0 fsz;
  SZBUF.free vs;
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
  #a:Type -> #b:Type0 -> len:size_t ->
  buf:SZBUF.buffer a{SZBUF.len buf = len} ->
  f:(b -> a -> Tot b) -> ib:b ->
  HST.ST b
    (requires (fun h0 -> SZBUF.live h0 buf))
    (ensures (fun h0 v h1 -> 
      h0 == h1 /\
      v == fold_left_seq (SZBUF.as_seq h0 buf) f ib))
    (decreases (SZBUF.length buf))
let rec fold_left_buffer #a #b len buf f ib =
  if len = sz0 then ib
  else (fold_left_buffer (len - sz1) (SZBUF.sub buf sz1 (len - sz1)) 
			 f (f ib (SZBUF.index buf sz0)))

val fold_left:
  #a:Type -> #b:Type0 -> vec:vector a -> 
  f:(b -> a -> Tot b) -> ib:b ->
  HST.ST b
    (requires (fun h0 -> live h0 vec))
    (ensures (fun h0 v h1 ->
      h0 == h1 /\
      v == fold_left_seq (as_seq h0 vec) f ib))
let fold_left #a #b vec f ib =
  fold_left_buffer (Vec?.sz vec) (SZBUF.sub (Vec?.vs vec) sz0 (Vec?.sz vec)) f ib

val forall_seq:
  #a:Type -> seq:S.seq a ->
  i:nat -> j:nat{i <= j && j <= S.length seq} ->
  p:(a -> GTot Type0) -> GTot Type0
let forall_seq #a seq i j p =
  forall (idx:nat{i <= idx && idx < j}). 
    p (S.index seq idx)

val forall_buffer:
  #a:Type -> h:HS.mem -> buf:SZBUF.buffer a ->
  i:nat -> j:nat{i <= j && j <= SZBUF.length buf} ->
  p:(a -> GTot Type0) -> GTot Type0
let forall_buffer #a h buf i j p =
  forall_seq (SZBUF.as_seq h buf) i j p

val forall_: 
  #a:Type -> h:HS.mem -> vec:vector a ->
  i:index_t -> j:index_t{i <= j && j <= size_of vec} ->
  p:(a -> Tot Type0) -> GTot Type0
let forall_ #a h vec i j p =
  forall_seq (as_seq h vec) (SZMOD.v i) (SZMOD.v j) p

val forall_all:
  #a:Type -> h:HS.mem -> vec:vector a ->
  p:(a -> Tot Type0) -> GTot Type0
let forall_all #a h vec p =
  forall_ h vec sz0 (size_of vec) p

val forall2_seq:
  #a:Type -> seq:S.seq a -> 
  i:nat -> j:nat{i <= j && j <= S.length seq} ->
  p:(a -> a -> GTot Type0) -> GTot Type0
let forall2_seq #a seq i j p =
  forall (k:nat{i <= k && k < j}) (l:nat{i <= l && l < j && k <> l}).
    p (S.index seq k) (S.index seq l)

val forall2_buffer:
  #a:Type -> h:HS.mem -> buf:SZBUF.buffer a ->
  i:nat -> j:nat{i <= j && j <= SZBUF.length buf} ->
  p:(a -> a -> GTot Type0) -> GTot Type0
let forall2_buffer #a h buf i j p =
  forall2_seq (SZBUF.as_seq h buf) i j p

val forall2:
  #a:Type -> h:HS.mem -> vec:vector a -> 
  i:index_t -> j:index_t{i <= j && j <= size_of vec} ->
  p:(a -> a -> GTot Type0) -> GTot Type0
let forall2 #a h vec i j p =
  forall2_seq (as_seq h vec) (SZMOD.v i) (SZMOD.v j) p

val forall2_all:
  #a:Type -> h:HS.mem -> vec:vector a -> 
  p:(a -> a -> GTot Type0) -> GTot Type0
let forall2_all #a h vec p =
  forall2 h vec sz0 (size_of vec) p

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
  #a:Type -> h:HS.mem -> buf:SZBUF.buffer a -> i:index_t{i < SZBUF.len buf} ->
  Lemma (SZBUF.get h buf (SZMOD.v i) == S.index (SZBUF.as_seq h (SZBUF.gsub buf i sz1)) 0)
let get_as_seq_index #a h buf i = ()

val get_preserved:
  #a:Type -> vec:vector a ->
  i:index_t{i < size_of vec} ->
  p:loc -> h0:HS.mem -> h1:HS.mem ->
  Lemma (requires (live h0 vec /\ 
		  loc_disjoint p (loc_vector_within vec i (i + sz1)) /\
		  modifies p h0 h1))
	(ensures (get h0 vec i == get h1 vec i))
let get_preserved #a vec i p h0 h1 =
  get_as_seq_index h0 (Vec?.vs vec) i;
  get_as_seq_index h1 (Vec?.vs vec) i

private val get_preserved_within:
  #a:Type -> vec:vector a ->
  i:index_t -> j:index_t{i <= j && j <= size_of vec} ->
  k:index_t{(k < i || j <= k) && k < size_of vec} ->
  h0:HS.mem -> h1:HS.mem ->
  Lemma (requires (live h0 vec /\
		  modifies (loc_vector_within vec i j) h0 h1))
	(ensures (get h0 vec k == get h1 vec k))
	[SMTPat (live h0 vec);
	SMTPat (modifies (loc_vector_within vec i j) h0 h1);
	SMTPat (get h0 vec k)]
let rec get_preserved_within #a vec i j k h0 h1 =
  if k < i then begin
    loc_vector_within_disjoint vec k (k + sz1) i j;
    get_preserved vec k (loc_vector_within vec i j) h0 h1
  end
  else begin
    loc_vector_within_disjoint vec i j k (k + sz1);
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
  #a:Type -> vec:vector a ->
  i:index_t -> j:index_t{i <= j && j <= size_of vec} ->
  p:(a -> Tot Type0) ->
  dloc:loc -> h0:HS.mem -> h1:HS.mem ->
  Lemma (requires (live h0 vec /\
		  loc_disjoint (loc_vector_within vec i j) dloc /\
		  forall_ h0 vec i j p /\
		  modifies dloc h0 h1))
	(ensures (forall_ h1 vec i j p))
let forall_preserved #a vec i j p dloc h0 h1 =
  modifies_as_seq_within vec i j dloc h0 h1;
  assert (S.slice (as_seq h0 vec) (SZMOD.v i) (SZMOD.v j) ==
	 S.slice (as_seq h1 vec) (SZMOD.v i) (SZMOD.v j))

val forall2_extend:
  #a:Type -> h:HS.mem -> vec:vector a ->
  i:index_t -> j:index_t{i <= j && j < size_of vec} ->
  p:(a -> a -> Tot Type0) ->
  Lemma (requires (forall2 h vec i j p /\
		  forall_ h vec i j 
		    (fun a -> p a (get h vec j) /\ p (get h vec j) a)))
	(ensures (forall2 h vec i (j + sz1) p))
let forall2_extend #a h vec i j p = ()

val forall2_forall_left:
  #a:Type -> h:HS.mem -> vec:vector a ->
  i:index_t -> j:index_t{i <= j && j <= size_of vec} ->
  k:index_t{i <= k && k < j} ->
  p:(a -> a -> Tot Type0) ->
  Lemma (requires (forall2 h vec i j p))
	(ensures (forall_ h vec i k (p (get h vec k))))
let forall2_forall_left #a h vec i j k p = ()

val forall2_forall_right:
  #a:Type -> h:HS.mem -> vec:vector a ->
  i:index_t -> j:index_t{i <= j && j <= size_of vec} ->
  k:index_t{i <= k && k < j} ->
  p:(a -> a -> Tot Type0) ->
  Lemma (requires (forall2 h vec i j p))
	(ensures (forall_ h vec (k + sz1) j (p (get h vec k))))
let forall2_forall_right #a h vec i j k p = ()


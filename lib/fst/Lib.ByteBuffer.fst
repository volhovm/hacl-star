module Lib.ByteBuffer

open FStar.HyperStack
open FStar.HyperStack.ST

open LowStar.Buffer

open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module B = LowStar.Buffer
module ByteSeq = Lib.ByteSequence

module Loops = Lib.LoopCombinators

friend Lib.ByteSequence

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 1"

let uint_to_be #t #l u =
  match t, l with
  | U1, _ -> u
  | U8, _ -> u
  | U16, SEC -> 
    RawIntTypes.u16_from_UInt16 (C.Endianness.htobe16 (RawIntTypes.u16_to_UInt16 u))
  | U16, PUB -> C.Endianness.htobe16 u
  | U32, SEC -> C.Endianness.htobe32 u
  | U64,_ -> C.Endianness.htobe64 u

let uint_to_le #t #l u =
  match t with
  | U1 -> u
  | U8 -> u
  | U16 -> C.Endianness.htole16 u
  | U32 -> C.Endianness.htole32 u
  | U64 -> C.Endianness.htole64 u

let uint_from_be #t #l u =
  match t with
  | U1 -> u
  | U8 -> u
  | U16 -> C.Endianness.be16toh u
  | U32 -> C.Endianness.be32toh u
  | U64 -> C.Endianness.be64toh u

let uint_from_le #t #l u =
  match t with
  | U1 -> u
  | U8 -> u
  | U16 -> C.Endianness.le16toh u
  | U32 -> C.Endianness.le32toh u
  | U64 -> C.Endianness.le64toh u

/// BEGIN Constant-time buffer equality

inline_for_extraction noextract
val cmp_bytes: 
    #len1:size_t 
  -> #len2:size_t 
  -> b1:lbuffer uint8 len1 
  -> b2:lbuffer uint8 len2 
  -> len:size_t{v len <= v len1 /\ v len <= v len2} 
  -> res:lbuffer uint8 (size 1) ->
  Stack uint8
    (requires fun h -> 
      live h b1 /\ live h b2 /\ live h res /\ disjoint res b1 /\ disjoint res b2 /\
      v (bget h res 0) == 255)    
    (ensures fun h0 z h1 -> 
      modifies1 res h0 h1 /\
      (as_seq h0 (gsub b1 0ul len) == as_seq h0 (gsub b2 0ul len)  ==> v z == 255) /\
      (as_seq h0 (gsub b1 0ul len) =!= as_seq h0 (gsub b2 0ul len) ==> v z == 0))
let rec cmp_bytes #len1 #len2 b1 b2 len res =
  let a_spec i = uint8 in
  let refl h = bget h res 0 in
  let footprint i = loc res in
  let spec h = 
  let h0 = ST.get() in
  loop h0 len a_spec refl footprint
    (fun i ->
      Loops.unfold_repeat_gen len a_spec (spec h0) (refl h0 0);
      let z0 = res.(0ul) in
      res.(0ul) <- eq_mask b1.(i) b2.(i) &. z0
    )


(*
  UInt.logand_lemma_1 #8 255;
  UInt.logand_lemma_2 #8 255;
  UInt.logand_lemma_1 #8 0;
  UInt.logand_lemma_2 #8 0;
  let h0 = ST.get() in
  let inv h (i:nat{i <= v len}) =
    let z = bget h res 0 in
    modifies1 res h0 h /\
    (as_seq h0 (gsub b1 0ul (size i)) == as_seq h0 (gsub b2 0ul (size i))  ==> v z == 255) /\
    (as_seq h0 (gsub b1 0ul (size i)) =!= as_seq h0 (gsub b2 0ul (size i)) ==> v z == 0)
  in
  Loops.for 0ul len inv 
    (fun i ->
      let z0 = res.(0ul) in
      res.(0ul) <- eq_mask b1.(i) b2.(i) &. z0;
      let h = ST.get() in
      if v (bget h res 0) = 255 then
        begin
        let s1 = as_seq h0 (gsub b1 0ul (i +! 1ul)) in
        let s2 = as_seq h0 (gsub b2 0ul (i +! 1ul)) in
        FStar.Seq.lemma_split s1 (v i);
        FStar.Seq.lemma_split s2 (v i);       
        Seq.lemma_eq_intro s1 s2
        end
      else if v z0 = 0 then
        lemma_not_equal_slice (as_seq h0 b1) (as_seq h0 b2) 0 (v i) (v i + 1)
      else
        lemma_not_equal_last (as_seq h0 b1) (as_seq h0 b2) 0 (v i + 1));
  res.(0ul)

let lbytes_eq #len b1 b2 =
  push_frame();
  let res = create 1ul (u8 255) in
  let z = cmp_bytes b1 b2 len res in
  pop_frame();
  z = u8 255

/// END Constant-time buffer equality

// TODO: Fix this
#set-options "--admit_smt_queries true"

let uint_from_bytes_le #t #l i =
  match t with
  | U8 -> i.(0ul)
  | U16 -> let u = C.load16_le i in u16_from_UInt16 u
  | U32 -> let u = C.load32_le i in u32_from_UInt32 u
  | U64 -> let u = C.load64_le i in u64_from_UInt64 u
  | U128 -> let u = C.load128_le i in u128_from_UInt128 u

let uint_from_bytes_be #t #l i =
  match t with
  | U8 -> i.(0ul)
  | U16 -> let u = C.load16_be i in u16_from_UInt16 u
  | U32 -> let u = C.load32_be i in u32_from_UInt32 u
  | U64 -> let u = C.load64_be i in u64_from_UInt64 u
  | U128 -> let u = C.load128_be i in u128_from_UInt128 u

let uint_to_bytes_le #t #l o i =
  match t with
  | U8 -> o.(0ul) <- i
  | U16 -> C.store16_le o (u16_to_UInt16 i)
  | U32 -> C.store32_le o (u32_to_UInt32 i)
  | U64 -> C.store64_le o (u64_to_UInt64 i)
  | U128 -> C.store128_le o (u128_to_UInt128 i)

let uint_to_bytes_be #t #l o i =
  match t with
  | U8 -> o.(0ul) <- i
  | U16 -> C.store16_be o (u16_to_UInt16 i)
  | U32 -> C.store32_be o (u32_to_UInt32 i)
  | U64 -> C.store64_be o (u64_to_UInt64 i)
  | U128 -> C.store128_be o (u128_to_UInt128 i)

inline_for_extraction
let uints_from_bytes_le #t #l #len o i =
  let h0 = ST.get() in
  let inv (h1:mem) (j:nat) =  True in
  let f' (j:size_t{0 <= v j /\ v j <= len}) : Stack unit
      (requires (fun h -> inv h (v j)))
      (ensures (fun h1 _ h2 -> inv h2 (v j + 1))) =
      let b_i = sub i (mul_mod j (size (numbytes t))) (size (numbytes t)) in
      let u_i = uint_from_bytes_le b_i in
      upd #_ #len o j u_i in
  Lib.Loops.for 0ul len inv f'

inline_for_extraction
let uints_from_bytes_be #t #l #len o i =
  let h0 = ST.get() in
  let inv (h1:mem) (j:nat) =  True in
  let f' (j:size_t{0 <= v j /\ v j <= len}) : Stack unit
      (requires (fun h -> inv h (v j)))
      (ensures (fun h1 _ h2 -> inv h2 (v j + 1))) =
      let b_i = sub i (mul_mod j (size (numbytes t))) (size (numbytes t)) in
      let u_i = uint_from_bytes_be b_i in
      upd #_ #len o j u_i in
  Lib.Loops.for 0ul len inv f'

inline_for_extraction
let uints_to_bytes_le #t #l len o i =
  let h0 = ST.get () in
  let inv (h1:mem) (j:nat) = True in
  let f' (j:size_t{0 <= v j /\ v j <= len}) : Stack unit
    (requires (fun h -> inv h (v j)))
    (ensures  (fun h1 _ h2 -> inv h2 (v j + 1))) =
      let u_i = i.(j) in
      let b_i = sub o (mul_mod j (size (numbytes t))) (size (numbytes t)) in
      uint_to_bytes_le b_i u_i in
  Lib.Loops.for 0ul len inv f'

inline_for_extraction
let uints_to_bytes_be #t #l len o i =
  let h0 = ST.get () in
  let inv (h1:mem) (j:nat) = True in
  let f' (j:size_t{0 <= v j /\ v j <= len}) : Stack unit
    (requires (fun h -> inv h (v j)))
    (ensures  (fun h1 _ h2 -> inv h2 (v j + 1))) =
      let u_i = i.(j) in
      let b_i = sub o (mul_mod j (size (numbytes t))) (size (numbytes t)) in
      uint_to_bytes_be b_i u_i in
  Lib.Loops.for 0ul len inv f'
*)

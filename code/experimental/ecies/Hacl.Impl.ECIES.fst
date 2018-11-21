module Hacl.Impl.ECIES

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
open Lib.LoopCombinators

module ST = FStar.HyperStack.ST
module Seq = Lib.Sequence
module Loops = Lib.LoopCombinators
module Spec = Spec.ECIES

(* module SHA2 = Hacl.Impl.SHA2_256 *)
(* module HMAC = Hacl.Impl.HMAC_SHA2_256 *)
(* module HKDF = Hacl.Impl.HKDF_SHA2_256 *)


assume val crypto_random: output:buffer uint8 -> len:size_t ->
  Stack bool
  (requires (fun h -> live h output))
  (ensures  (fun h0 _ h1 -> modifies1 output h0 h1))



///
/// Curve25519, AES128_GCM and HKDF_SHA2_256
///

let ciphersuite = Spec.DH.DH_Curve25519, Spec.AEAD.AEAD_AES128_GCM, Spec.Hash.SHA2_256
let id_of_ciphersuite = u8 0

///
/// Constants
///

inline_for_extraction
let size_nonce = size Spec.ECIES.size_nonce

inline_for_extraction
let size_key = size Spec.ECIES.size_key

inline_for_extraction
let size_context = size Spec.ECIES.size_context

inline_for_extraction
let size_info = size Spec.ECIES.size_info

inline_for_extraction
let size_key_dh = size Spec.ECIES.size_key_dh

///
/// Types
///

type key_public_p = lbuffer uint8 size_key_dh
type key_private_p = lbuffer uint8 size_key_dh
type key_p = lbuffer uint8 size_key

///
/// Implementation
///

let const_label_nonce: x:ilbuffer size_t (size size_label_nonce)){witnessed x Spec.ECIES.const_lable_nonce /\ recallable x} =
  createL_global Spec.ECIES.list_label_nonce

let const_label_key: x:ilbuffer size_t (size size_label_key)){witnessed x Spec.ECIES.const_lable_key /\ recallable x} =
  createL_global Spec.ECIES.list_label_key



val encap:
    output: lbuffer uint8 (1ul +. size_key +. 2ul *. size_key_dh)
  -> kpub: key_public_p
  -> context: lbuffer uint8 size_context ->
  Stack unit
  (requires (fun h -> live h output /\ live h kpub /\ live h context
                 /\ disjoint output kpub /\ disjoint output context))
  (ensures  (fun h0 _ h1 -> modifies1 output h0 h1))

let encap output kpub context =
  push_frame ();
  let flag = sub output (size 0) (size 1) in
  let key = sub output (size 1) size_key in
  let eph_kpub = sub output (1ul +. size_key) size_key_public in
  let eph_kpriv = sub output (1ul +. size_key +. size_key_public) size_key_private in
  let extracted = create size_key (u8 0) in
  let secret = create size_key (u8 0) in
  let salt = create (2ul *. size_key_public) (u8 0) in
  let info = create size_info (u8 0) in
  let res0 = crypto_random eph_kpriv size_key_private in
  let res1 = secret_to_public eph_kpub eph_kpriv in
  let res2 = DH.dh secret eph_kpriv kpub in
  update_sub salt (size 0) size_key_public eph_kpub;
  update_sub salt size_key_public size_key_public kpub;
  HKDF.extract extracted salt (2ul *. size_key_public) secret size_secret;
  info.(0ul) <- id_of_ciphersuite;
  update_sub info (size 1) size_label_key const_label_key;
  update_sub info size_label_key size_context context;
  HKDF.expand key extracted size_secret info size_info size_key;
  if res0 && res1 && res2 then output.(0ul) <- (u8 0) else output.(0ul) <- (u8 1);
  pop_frame ()


val decap:
    output: lbuffer uint8 (size_key +. 1ul)
  -> kpriv: key_private_p
  -> eph_kpub: key_public_p
  -> context: lbuffer uint8 size_context
  Stack unit
  (requires (fun h -> live h output /\ live h kpriv /\ live h eph_kpub /\ live h context))
  (ensures  (fun h0 _ h1 -> modifies1 output h0 h1))

let decap output kpriv eph_kpub context =
  push_frame();
  let kpub = create size_key_public (u8 0) in
  let salt = create (2ul *. size_key_public) (u8 0) in
  let info = create size_info (u8 0) in
  let extracted = create size_key (u8 0) in
  let flag = sub output (size 0) (size 1) in
  let secret = sub output (size 1) size_secret in
  let res1 = secret_to_public kpub kpriv in
  let res2 = DH.dh secret kpriv eph_kpub in
  update_sub salt (size 0) size_key_public eph_kpub;
  update_sub salt size_key_public size_key_public kpub;
  HKDF.extract extracted salt (2ul *. size_key_public) secret size_secret;
  info.(0ul) <- id_of_ciphersuite;
  update_sub info (size 1) size_label_key const_label_key;
  update_sub info size_label_key size_context context;
  HKDF.expand secret extracted size_secret info size_info size_key;
  pop_frame()



val encrypt:
    cs: ciphersuite
  -> sk: key_s cs
  -> input: bytes{length input <= max_size_t
           /\ length input + AEAD.size_block (aead_of_cs cs) <= max_size_t
           /\ length input + AEAD.padlen (aead_of_cs cs) (length input) <= max_size_t}
  -> aad: bytes {length aad <= max_size_t /\ length aad + AEAD.padlen (aead_of_cs cs) (length aad) <= max_size_t}
  -> counter: uint32 ->
  Tot bytes

let encrypt cs sk input aad counter =
  let klen = AEAD.size_key (aead_of_cs cs) in
  let key = sub sk 0 klen in
  let nonce = sub sk klen (size_nonce cs - numbytes U32) in
  let ctr = uint_to_bytes_le counter in
  AEAD.aead_encrypt (aead_of_cs cs) key (nonce @| ctr) input aad


val encrypt:
    output: buffer uint8
  -> sk: key_secret_s
  -> input: buffer uint8
  -> len: size_t{v len == length input
               /\ length input <= max_size_t
               /\ length input + AEAD.size_block (aead_of_cs cs) <= max_size_t
               /\ length input + AEAD.padlen (aead_of_cs cs) (length input) <= max_size_t}
  -> aad: buffer uint8
  -> alen: size_t{v alen == length aad
               /\ length aad <= max_size_t
               /\ length aad + AEAD.padlen (aead_of_cs cs) (length aad) <= max_size_t}
  -> counter: uint32 ->
  Stack unit
  (requires (fun h -> live h output /\ live h sk /\ live h input /\ live h aad
                 /\ disjoint output sk /\ disjoint output input /\ disjoint output aad))
  (ensures  (fun h0 _ h1 -> modifies1 output h0 h1))

let encrypt output sk input len aad alen counter =
  push_frame();
  let ctr8 = create (numbytes U32) (u8 0) in
  let key = sub sk (size 0) size_

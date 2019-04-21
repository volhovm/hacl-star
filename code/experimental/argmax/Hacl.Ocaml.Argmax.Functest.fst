module Hacl.Ocaml.Argmax.Functest

open FStar.All
open FStar.IO
open FStar.Mul

open Hacl.Argmax.Common

module GM = Hacl.Argmax.GM
module P = Hacl.Argmax.Paillier
module U64 = FStar.UInt64

// TODO Provide actually correct values

val test_gm: unit -> ML unit
let test_gm () =
  let q:prm = admit(); 7 in
  let p:prm = admit(); 11 in
  let n = p * q in
  let y:fe n = 5 in
  assume (GM.is_nonsq y);
  // 5 is square modulo 11, but not modulo 7
  let sec = GM.Secret p q y in
  let pub = GM.s2p sec in
  let r:fe n = 6 in
  assert (sqr r = 36);
  assert (36 < n);
  assert (sqr r *% y = 26);
  assert (sqr r > 0 /\ sqr r *% y > 0);
  let m = false in
  let c = GM.encrypt pub r m in
  let m' = GM.decrypt sec c in
  print_string "GM:\n";
  print_string "* mesage: ";
  print_string (if m then "true" else "false");
  print_string "\n* ciphertext: ";
  print_uint64 (U64.uint_to_t c);
  print_string "\n* decrypted: ";
  print_string (if m' then "true" else "false");
  print_string "\nGM test done\n"

val test_paillier: unit -> ML unit
let test_paillier () =
  let q:prm = admit(); 7 in
  let p:prm = admit(); 11 in
  let n = p * q in
  let g:P.isg n = admit(); 6 in
  let sec = P.Secret p q g in
  let pub = P.s2p sec in
  let m:fe n = 4 in
  let r:fe n = 3 in
  assume (isunit r);
  let c = P.encrypt pub r m in
  let m' = P.decrypt sec c in
  print_string "Paillier test done\n"

val main: unit
let main =
  test_gm ()
//  test_paillier ()

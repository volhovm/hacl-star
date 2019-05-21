module Hacl.Test.RSA

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.Lib
open Hacl.Impl.Convert
open Hacl.RSAPSS

module ST = FStar.HyperStack.ST

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val u8: n:nat{n < 0x100} -> uint8
let u8 n = u8 n

val ctest:
    pow2_i:size_t
  -> modBits:size_t{v modBits > 0}
  -> n:ilbuffer uint8 (blocks modBits 8ul)
  -> pkeyBits:size_t{v pkeyBits > 0}
  -> e:ilbuffer uint8 (blocks pkeyBits 8ul)
  -> skeyBits:size_t{v skeyBits > 0}
  -> d:ilbuffer uint8 (blocks skeyBits 8ul)
  -> pTLen:size_t{v pTLen > 0}
  -> p:ilbuffer uint8 pTLen
  -> qTLen:size_t{v qTLen > 0}
  -> q:ilbuffer uint8 qTLen
  -> r2:ilbuffer uint8 (blocks modBits 8ul)
  -> rBlindTLen:size_t{v rBlindTLen > 0}
  -> rBlind:ilbuffer uint8 rBlindTLen
  -> msgLen:size_t
  -> msg:ilbuffer uint8 msgLen
  -> saltLen:size_t
  -> salt:ilbuffer uint8 saltLen
  -> sgnt_expected:ilbuffer uint8 (blocks modBits 8ul)
  -> Stack bool
    (requires fun h ->
      live h n /\ live h e /\ live h d /\ live h p /\ live h q /\
      live h r2 /\ live h rBlind /\ live h msg /\ live h salt /\
      live h sgnt_expected)
    (ensures  fun h0 r h1 -> True)
let ctest pow2_i modBits n pkeyBits e skeyBits d pTLen p qTLen q r2 rBlindTLen rBlind msgLen msg saltLen salt sgnt_expected =
  admit();
  push_frame ();
  //let pow2_i = size (pow2 (x0 - 6)) in
  let nLen = blocks modBits 64ul in
  let eLen = blocks pkeyBits 64ul in
  let dLen = blocks skeyBits 64ul in
  let pLen = blocks pTLen 8ul in
  let qLen = blocks qTLen 8ul in
  let rBlindLen = blocks rBlindTLen 8ul in

  let pkeyLen = nLen +. eLen +. nLen in
  let skeyLen: size_t = pkeyLen +. dLen +. pLen +. qLen in
  assume (v skeyLen > 0);
  let skey = create skeyLen (u64 0) in

  let nNat = sub skey 0ul nLen in
  let eNat = sub skey nLen eLen in
  let r2Nat =sub skey (nLen +. eLen) nLen in
  let dNat = sub skey pkeyLen dLen in
  let pNat = sub skey (pkeyLen +. dLen) pLen in
  let qNat = sub skey (pkeyLen +. dLen +. pLen) qLen in


  text_to_nat (blocks modBits 8ul) n nNat;
  text_to_nat (blocks pkeyBits 8ul) e eNat;
  text_to_nat (blocks modBits 8ul) r2 r2Nat;
  text_to_nat (blocks skeyBits 8ul) d dNat;
  text_to_nat pTLen p pNat;
  text_to_nat qTLen q qNat;

  let pkey = sub skey 0ul pkeyLen in

  let rBlindNat = create rBlindLen (u64 0) in
  text_to_nat rBlindTLen rBlind rBlindNat;
  let rBlind0 = rBlindNat.(0ul) in

  let nTLen = blocks modBits 8ul in
  let sgnt = create nTLen (u8 0) in
  rsa_pss_sign pow2_i modBits pkeyBits skeyBits pLen qLen skey rBlind0 saltLen salt msgLen msg sgnt;
  let check_sgnt = Lib.ByteBuffer.lbytes_eq #nTLen sgnt sgnt_expected in
  let verify_sgnt = rsa_pss_verify pow2_i modBits pkeyBits pkey saltLen sgnt msgLen msg in
  Lib.PrintBuffer.print_compare_display nTLen sgnt sgnt_expected;
  let res = check_sgnt && verify_sgnt in
  pop_frame ();
  res

//
// Test1
//
let test1_n: b:ilbuffer uint8 128ul{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8
    [0xa5; 0x6e; 0x4a; 0x0e; 0x70; 0x10; 0x17; 0x58; 0x9a; 0x51; 0x87; 0xdc; 0x7e; 0xa8; 0x41; 0xd1;
     0x56; 0xf2; 0xec; 0x0e; 0x36; 0xad; 0x52; 0xa4; 0x4d; 0xfe; 0xb1; 0xe6; 0x1f; 0x7a; 0xd9; 0x91;
     0xd8; 0xc5; 0x10; 0x56; 0xff; 0xed; 0xb1; 0x62; 0xb4; 0xc0; 0xf2; 0x83; 0xa1; 0x2a; 0x88; 0xa3;
     0x94; 0xdf; 0xf5; 0x26; 0xab; 0x72; 0x91; 0xcb; 0xb3; 0x07; 0xce; 0xab; 0xfc; 0xe0; 0xb1; 0xdf;
     0xd5; 0xcd; 0x95; 0x08; 0x09; 0x6d; 0x5b; 0x2b; 0x8b; 0x6d; 0xf5; 0xd6; 0x71; 0xef; 0x63; 0x77;
     0xc0; 0x92; 0x1c; 0xb2; 0x3c; 0x27; 0x0a; 0x70; 0xe2; 0x59; 0x8e; 0x6f; 0xf8; 0x9d; 0x19; 0xf1;
     0x05; 0xac; 0xc2; 0xd3; 0xf0; 0xcb; 0x35; 0xf2; 0x92; 0x80; 0xe1; 0x38; 0x6b; 0x6f; 0x64; 0xc4;
     0xef; 0x22; 0xe1; 0xe1; 0xf2; 0x0d; 0x0c; 0xe8; 0xcf; 0xfb; 0x22; 0x49; 0xbd; 0x9a; 0x21; 0x37])
  in
  assert_norm (List.Tot.length l == 128);
  createL_global l

let test1_e: b:ilbuffer uint8 3ul{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [0x01; 0x00; 0x01]) in
  assert_norm (List.Tot.length l == 3);
  createL_global l

let test1_d: b:ilbuffer uint8 128ul{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8
    [0x33; 0xa5; 0x04; 0x2a; 0x90; 0xb2; 0x7d; 0x4f; 0x54; 0x51; 0xca; 0x9b; 0xbb; 0xd0; 0xb4; 0x47;
     0x71; 0xa1; 0x01; 0xaf; 0x88; 0x43; 0x40; 0xae; 0xf9; 0x88; 0x5f; 0x2a; 0x4b; 0xbe; 0x92; 0xe8;
     0x94; 0xa7; 0x24; 0xac; 0x3c; 0x56; 0x8c; 0x8f; 0x97; 0x85; 0x3a; 0xd0; 0x7c; 0x02; 0x66; 0xc8;
     0xc6; 0xa3; 0xca; 0x09; 0x29; 0xf1; 0xe8; 0xf1; 0x12; 0x31; 0x88; 0x44; 0x29; 0xfc; 0x4d; 0x9a;
     0xe5; 0x5f; 0xee; 0x89; 0x6a; 0x10; 0xce; 0x70; 0x7c; 0x3e; 0xd7; 0xe7; 0x34; 0xe4; 0x47; 0x27;
     0xa3; 0x95; 0x74; 0x50; 0x1a; 0x53; 0x26; 0x83; 0x10; 0x9c; 0x2a; 0xba; 0xca; 0xba; 0x28; 0x3c;
     0x31; 0xb4; 0xbd; 0x2f; 0x53; 0xc3; 0xee; 0x37; 0xe3; 0x52; 0xce; 0xe3; 0x4f; 0x9e; 0x50; 0x3b;
     0xd8; 0x0c; 0x06; 0x22; 0xad; 0x79; 0xc6; 0xdc; 0xee; 0x88; 0x35; 0x47; 0xc6; 0xa3; 0xb3; 0x25])
  in
  assert_norm (List.Tot.length l == 128);
  createL_global l

let test1_p: b:ilbuffer uint8 64ul{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8
    [0xe7; 0xe8; 0x94; 0x27; 0x20; 0xa8; 0x77; 0x51; 0x72; 0x73; 0xa3; 0x56; 0x05; 0x3e; 0xa2; 0xa1;
     0xbc; 0x0c; 0x94; 0xaa; 0x72; 0xd5; 0x5c; 0x6e; 0x86; 0x29; 0x6b; 0x2d; 0xfc; 0x96; 0x79; 0x48;
     0xc0; 0xa7; 0x2c; 0xbc; 0xcc; 0xa7; 0xea; 0xcb; 0x35; 0x70; 0x6e; 0x09; 0xa1; 0xdf; 0x55; 0xa1;
     0x53; 0x5b; 0xd9; 0xb3; 0xcc; 0x34; 0x16; 0x0b; 0x3b; 0x6d; 0xcd; 0x3e; 0xda; 0x8e; 0x64; 0x43])
  in
  assert_norm (List.Tot.length l == 64);
  createL_global l

let test1_q: b:ilbuffer uint8 64ul{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8
    [0xb6; 0x9d; 0xca; 0x1c; 0xf7; 0xd4; 0xd7; 0xec; 0x81; 0xe7; 0x5b; 0x90; 0xfc; 0xca; 0x87; 0x4a;
     0xbc; 0xde; 0x12; 0x3f; 0xd2; 0x70; 0x01; 0x80; 0xaa; 0x90; 0x47; 0x9b; 0x6e; 0x48; 0xde; 0x8d;
     0x67; 0xed; 0x24; 0xf9; 0xf1; 0x9d; 0x85; 0xba; 0x27; 0x58; 0x74; 0xf5; 0x42; 0xcd; 0x20; 0xdc;
     0x72; 0x3e; 0x69; 0x63; 0x36; 0x4a; 0x1f; 0x94; 0x25; 0x45; 0x2b; 0x26; 0x9a; 0x67; 0x99; 0xfd])
  in
  assert_norm (List.Tot.length l == 64);
  createL_global l

let test1_r2: b:ilbuffer uint8 128ul{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8
    [0x88; 0xb6; 0x2d; 0x5d; 0x22; 0x94; 0x29; 0xd9; 0xbc; 0x2c; 0x5e; 0x1f; 0xa8; 0xf1; 0x08; 0x31;
     0x77; 0xcd; 0xc6; 0x43; 0x6d; 0xea; 0xf5; 0x22; 0xc9; 0xe6; 0xff; 0xf5; 0xe5; 0xf4; 0x86; 0x7f;
     0xc0; 0xa1; 0x3b; 0x73; 0xb8; 0x8b; 0x0d; 0x97; 0x1e; 0x7c; 0xda; 0xf6; 0x6e; 0xea; 0xf3; 0xb2;
     0x1d; 0xa4; 0x56; 0x8d; 0xa5; 0x92; 0x04; 0x9f; 0x7c; 0xe0; 0x76; 0xe0; 0x1e; 0x63; 0x0c; 0x2c;
     0x6f; 0x12; 0xd2; 0x12; 0xd6; 0xec; 0x65; 0x54; 0xa0; 0x70; 0x5c; 0x63; 0x48; 0xca; 0xce; 0xff;
     0xe9; 0xeb; 0x3e; 0x0b; 0xf9; 0xff; 0xe3; 0xfa; 0x64; 0x80; 0x17; 0x31; 0x27; 0xd0; 0x2f; 0x60;
     0x04; 0xa5; 0xbf; 0x2f; 0xa4; 0x16; 0x66; 0x66; 0x3d; 0xab; 0x4f; 0x0a; 0x82; 0x0d; 0xa3; 0xb3;
     0x26; 0xd3; 0x5f; 0xea; 0xc6; 0x28; 0xf4; 0xc5; 0x27; 0x4b; 0xa3; 0x5f; 0xa7; 0xc0; 0x32; 0x60])
  in
  assert_norm (List.Tot.length l == 128);
  createL_global l

let test1_rBlind: b:ilbuffer uint8 8ul{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8
    [0xbb; 0x34; 0x64; 0x01; 0x1c; 0x30; 0x3a; 0xd9])
  in
  assert_norm (List.Tot.length l == 8);
  createL_global l

let test1_msg: b:ilbuffer uint8 51ul{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8
    [0x85; 0x13; 0x84; 0xcd; 0xfe; 0x81; 0x9c; 0x22; 0xed; 0x6c; 0x4c; 0xcb; 0x30; 0xda; 0xeb; 0x5c;
     0xf0; 0x59; 0xbc; 0x8e; 0x11; 0x66; 0xb7; 0xe3; 0x53; 0x0c; 0x4c; 0x23; 0x3e; 0x2b; 0x5f; 0x8f;
     0x71; 0xa1; 0xcc; 0xa5; 0x82; 0xd4; 0x3e; 0xcc; 0x72; 0xb1; 0xbc; 0xa1; 0x6d; 0xfc; 0x70; 0x13;
     0x22; 0x6b; 0x9e])
  in
  assert_norm (List.Tot.length l == 51);
  createL_global l

let test1_salt: b:ilbuffer uint8 20ul{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8
    [0xef; 0x28; 0x69; 0xfa; 0x40; 0xc3; 0x46; 0xcb; 0x18; 0x3d; 0xab; 0x3d; 0x7b; 0xff; 0xc9; 0x8f;
     0xd5; 0x6d; 0xf4; 0x2d])
  in
  assert_norm (List.Tot.length l == 20);
  createL_global l

let test1_sgnt_expected: b:ilbuffer uint8 128ul{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8
    [0x62; 0xeb; 0xb8; 0x03; 0x3a; 0x2d; 0x0b; 0x8b; 0xec; 0x42; 0x56; 0x52; 0x29; 0x9b; 0x3f; 0x02;
     0x8f; 0xa8; 0x0c; 0x28; 0x11; 0x0d; 0xf5; 0x37; 0x47; 0x2e; 0x5e; 0xd6; 0x28; 0x62; 0xb9; 0x98;
     0x36; 0xe5; 0x7a; 0xa9; 0x8d; 0x4b; 0x94; 0x9a; 0x21; 0xf0; 0x21; 0xee; 0x33; 0x89; 0xff; 0x52;
     0x66; 0xe0; 0x54; 0xd4; 0x4e; 0x8c; 0x92; 0x48; 0x0a; 0xc9; 0x10; 0x67; 0xde; 0xfb; 0xae; 0xd4;
     0xdc; 0x3c; 0xe2; 0x43; 0xe8; 0x17; 0x52; 0x66; 0xd3; 0xec; 0x69; 0xfd; 0xb0; 0xed; 0xea; 0xc1;
     0x1c; 0x8c; 0x9e; 0x3e; 0x99; 0x41; 0x54; 0xa9; 0x33; 0x95; 0xa5; 0x11; 0xb4; 0xa1; 0x72; 0xf6;
     0x64; 0x4f; 0x37; 0xf6; 0x80; 0x7b; 0x86; 0x71; 0x6f; 0xc9; 0x07; 0xe1; 0xd0; 0xfc; 0x75; 0xbd;
     0xa7; 0x7e; 0x41; 0x1b; 0xfc; 0x60; 0xfd; 0x2e; 0xd9; 0x27; 0x8e; 0x92; 0x1a; 0x33; 0x02; 0x1f])
  in
  assert_norm (List.Tot.length l == 128);
  createL_global l


//
// Test2
//
let test2_n: b:ilbuffer uint8 129ul{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8
    [0x01; 0xd4; 0x0c; 0x1b; 0xcf; 0x97; 0xa6; 0x8a; 0xe7; 0xcd; 0xbd; 0x8a; 0x7b; 0xf3; 0xe3; 0x4f;
     0xa1; 0x9d; 0xcc; 0xa4; 0xef; 0x75; 0xa4; 0x74; 0x54; 0x37; 0x5f; 0x94; 0x51; 0x4d; 0x88; 0xfe;
     0xd0; 0x06; 0xfb; 0x82; 0x9f; 0x84; 0x19; 0xff; 0x87; 0xd6; 0x31; 0x5d; 0xa6; 0x8a; 0x1f; 0xf3;
     0xa0; 0x93; 0x8e; 0x9a; 0xbb; 0x34; 0x64; 0x01; 0x1c; 0x30; 0x3a; 0xd9; 0x91; 0x99; 0xcf; 0x0c;
     0x7c; 0x7a; 0x8b; 0x47; 0x7d; 0xce; 0x82; 0x9e; 0x88; 0x44; 0xf6; 0x25; 0xb1; 0x15; 0xe5; 0xe9;
     0xc4; 0xa5; 0x9c; 0xf8; 0xf8; 0x11; 0x3b; 0x68; 0x34; 0x33; 0x6a; 0x2f; 0xd2; 0x68; 0x9b; 0x47;
     0x2c; 0xbb; 0x5e; 0x5c; 0xab; 0xe6; 0x74; 0x35; 0x0c; 0x59; 0xb6; 0xc1; 0x7e; 0x17; 0x68; 0x74;
     0xfb; 0x42; 0xf8; 0xfc; 0x3d; 0x17; 0x6a; 0x01; 0x7e; 0xdc; 0x61; 0xfd; 0x32; 0x6c; 0x4b; 0x33;
     0xc9])
  in
  assert_norm (List.Tot.length l == 129);
  createL_global l

let test2_e: b:ilbuffer uint8 3ul{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [0x01; 0x00; 0x01]) in
  assert_norm (List.Tot.length l == 3);
  createL_global l

let test2_d: b:ilbuffer uint8 128ul{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8
    [0x02; 0x7d; 0x14; 0x7e; 0x46; 0x73; 0x05; 0x73; 0x77; 0xfd; 0x1e; 0xa2; 0x01; 0x56; 0x57; 0x72;
     0x17; 0x6a; 0x7d; 0xc3; 0x83; 0x58; 0xd3; 0x76; 0x04; 0x56; 0x85; 0xa2; 0xe7; 0x87; 0xc2; 0x3c;
     0x15; 0x57; 0x6b; 0xc1; 0x6b; 0x9f; 0x44; 0x44; 0x02; 0xd6; 0xbf; 0xc5; 0xd9; 0x8a; 0x3e; 0x88;
     0xea; 0x13; 0xef; 0x67; 0xc3; 0x53; 0xec; 0xa0; 0xc0; 0xdd; 0xba; 0x92; 0x55; 0xbd; 0x7b; 0x8b;
     0xb5; 0x0a; 0x64; 0x4a; 0xfd; 0xfd; 0x1d; 0xd5; 0x16; 0x95; 0xb2; 0x52; 0xd2; 0x2e; 0x73; 0x18;
     0xd1; 0xb6; 0x68; 0x7a; 0x1c; 0x10; 0xff; 0x75; 0x54; 0x5f; 0x3d; 0xb0; 0xfe; 0x60; 0x2d; 0x5f;
     0x2b; 0x7f; 0x29; 0x4e; 0x36; 0x01; 0xea; 0xb7; 0xb9; 0xd1; 0xce; 0xcd; 0x76; 0x7f; 0x64; 0x69;
     0x2e; 0x3e; 0x53; 0x6c; 0xa2; 0x84; 0x6c; 0xb0; 0xc2; 0xdd; 0x48; 0x6a; 0x39; 0xfa; 0x75; 0xb1])
  in
  assert_norm (List.Tot.length l == 128);
  createL_global l

let test2_p: b:ilbuffer uint8 65ul{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8
    [0x01; 0x66; 0x01; 0xe9; 0x26; 0xa0; 0xf8; 0xc9; 0xe2; 0x6e; 0xca; 0xb7; 0x69; 0xea; 0x65; 0xa5;
     0xe7; 0xc5; 0x2c; 0xc9; 0xe0; 0x80; 0xef; 0x51; 0x94; 0x57; 0xc6; 0x44; 0xda; 0x68; 0x91; 0xc5;
     0xa1; 0x04; 0xd3; 0xea; 0x79; 0x55; 0x92; 0x9a; 0x22; 0xe7; 0xc6; 0x8a; 0x7a; 0xf9; 0xfc; 0xad;
     0x77; 0x7c; 0x3c; 0xcc; 0x2b; 0x9e; 0x3d; 0x36; 0x50; 0xbc; 0xe4; 0x04; 0x39; 0x9b; 0x7e; 0x59;
     0xd1])
  in
  assert_norm (List.Tot.length l == 65);
  createL_global l

let test2_q: b:ilbuffer uint8 65ul{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8
    [0x01; 0x4e; 0xaf; 0xa1; 0xd4; 0xd0; 0x18; 0x4d; 0xa7; 0xe3; 0x1f; 0x87; 0x7d; 0x12; 0x81; 0xdd;
     0xda; 0x62; 0x56; 0x64; 0x86; 0x9e; 0x83; 0x79; 0xe6; 0x7a; 0xd3; 0xb7; 0x5e; 0xae; 0x74; 0xa5;
     0x80; 0xe9; 0x82; 0x7a; 0xbd; 0x6e; 0xb7; 0xa0; 0x02; 0xcb; 0x54; 0x11; 0xf5; 0x26; 0x67; 0x97;
     0x76; 0x8f; 0xb8; 0xe9; 0x5a; 0xe4; 0x0e; 0x3e; 0x8a; 0x01; 0xf3; 0x5f; 0xf8; 0x9e; 0x56; 0xc0;
     0x79])
  in
  assert_norm (List.Tot.length l == 65);
  createL_global l

let test2_r2: b:ilbuffer uint8 129ul{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8
    [0x00; 0x3c; 0xa6; 0xd8; 0xd8; 0x1d; 0x98; 0xc0; 0xef; 0x8c; 0x89; 0x01; 0x3b; 0x40; 0x19; 0x4f;
     0x83; 0x85; 0x28; 0x63; 0x67; 0x71; 0x53; 0x2a; 0x4b; 0x76; 0xf7; 0x4a; 0xbe; 0x84; 0xd9; 0x9d;
     0x92; 0xbf; 0x73; 0x16; 0xdc; 0xbd; 0x1c; 0x3b; 0xc8; 0x14; 0x8c; 0x54; 0x9a; 0xa1; 0xfc; 0x3b;
     0x12; 0xe5; 0x2e; 0xe3; 0xe4; 0xee; 0x59; 0x00; 0x03; 0xa1; 0x38; 0xcb; 0x21; 0xae; 0xe4; 0x06;
     0x99; 0x74; 0xc6; 0x2c; 0x4c; 0x75; 0xff; 0xfb; 0x2e; 0x1b; 0x45; 0x5c; 0x80; 0xb9; 0x20; 0xc5;
     0x80; 0x92; 0xb6; 0xea; 0x3e; 0x74; 0x01; 0x3d; 0x74; 0xc2; 0xbf; 0xb2; 0xcf; 0x36; 0xb3; 0x84;
     0xd6; 0xc0; 0xac; 0xee; 0xb5; 0xee; 0x62; 0x8f; 0xa7; 0x39; 0x0f; 0xa1; 0x86; 0x7b; 0xe4; 0xa3;
     0xbe; 0xd2; 0x84; 0x59; 0xa1; 0x80; 0x3f; 0x72; 0xf3; 0x2d; 0x10; 0x90; 0x2a; 0xb8; 0x5b; 0x1a;
     0x52])
  in
  assert_norm (List.Tot.length l == 129);
  createL_global l

let test2_rBlind: b:ilbuffer uint8 8ul{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8
    [0x35; 0x26; 0x91; 0xc5; 0x24; 0xf6; 0xdd; 0x8e])
  in
  assert_norm (List.Tot.length l == 8);
  createL_global l

let test2_msg: b:ilbuffer uint8 234ul{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8
    [0xe4; 0xf8; 0x60; 0x1a; 0x8a; 0x6d; 0xa1; 0xbe; 0x34; 0x44; 0x7c; 0x09; 0x59; 0xc0; 0x58; 0x57;
     0x0c; 0x36; 0x68; 0xcf; 0xd5; 0x1d; 0xd5; 0xf9; 0xcc; 0xd6; 0xad; 0x44; 0x11; 0xfe; 0x82; 0x13;
     0x48; 0x6d; 0x78; 0xa6; 0xc4; 0x9f; 0x93; 0xef; 0xc2; 0xca; 0x22; 0x88; 0xce; 0xbc; 0x2b; 0x9b;
     0x60; 0xbd; 0x04; 0xb1; 0xe2; 0x20; 0xd8; 0x6e; 0x3d; 0x48; 0x48; 0xd7; 0x09; 0xd0; 0x32; 0xd1;
     0xe8; 0xc6; 0xa0; 0x70; 0xc6; 0xaf; 0x9a; 0x49; 0x9f; 0xcf; 0x95; 0x35; 0x4b; 0x14; 0xba; 0x61;
     0x27; 0xc7; 0x39; 0xde; 0x1b; 0xb0; 0xfd; 0x16; 0x43; 0x1e; 0x46; 0x93; 0x8a; 0xec; 0x0c; 0xf8;
     0xad; 0x9e; 0xb7; 0x2e; 0x83; 0x2a; 0x70; 0x35; 0xde; 0x9b; 0x78; 0x07; 0xbd; 0xc0; 0xed; 0x8b;
     0x68; 0xeb; 0x0f; 0x5a; 0xc2; 0x21; 0x6b; 0xe4; 0x0c; 0xe9; 0x20; 0xc0; 0xdb; 0x0e; 0xdd; 0xd3;
     0x86; 0x0e; 0xd7; 0x88; 0xef; 0xac; 0xca; 0xca; 0x50; 0x2d; 0x8f; 0x2b; 0xd6; 0xd1; 0xa7; 0xc1;
     0xf4; 0x1f; 0xf4; 0x6f; 0x16; 0x81; 0xc8; 0xf1; 0xf8; 0x18; 0xe9; 0xc4; 0xf6; 0xd9; 0x1a; 0x0c;
     0x78; 0x03; 0xcc; 0xc6; 0x3d; 0x76; 0xa6; 0x54; 0x4d; 0x84; 0x3e; 0x08; 0x4e; 0x36; 0x3b; 0x8a;
     0xcc; 0x55; 0xaa; 0x53; 0x17; 0x33; 0xed; 0xb5; 0xde; 0xe5; 0xb5; 0x19; 0x6e; 0x9f; 0x03; 0xe8;
     0xb7; 0x31; 0xb3; 0x77; 0x64; 0x28; 0xd9; 0xe4; 0x57; 0xfe; 0x3f; 0xbc; 0xb3; 0xdb; 0x72; 0x74;
     0x44; 0x2d; 0x78; 0x58; 0x90; 0xe9; 0xcb; 0x08; 0x54; 0xb6; 0x44; 0x4d; 0xac; 0xe7; 0x91; 0xd7;
     0x27; 0x3d; 0xe1; 0x88; 0x97; 0x19; 0x33; 0x8a; 0x77; 0xfe])
  in
  assert_norm (List.Tot.length l == 234);
  createL_global l

let test2_salt: b:ilbuffer uint8 20ul{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8
    [0x7f; 0x6d; 0xd3; 0x59; 0xe6; 0x04; 0xe6; 0x08; 0x70; 0xe8; 0x98; 0xe4; 0x7b; 0x19; 0xbf; 0x2e;
     0x5a; 0x7b; 0x2a; 0x90])
  in
  assert_norm (List.Tot.length l == 20);
  createL_global l

let test2_sgnt_expected: b:ilbuffer uint8 129ul{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8
    [0x01; 0x90; 0x44; 0x7a; 0x91; 0xa3; 0xef; 0x1e; 0x9a; 0x36; 0x44; 0xb2; 0x2d; 0xb0; 0x9d; 0xb3;
     0x7b; 0x45; 0xe1; 0xd5; 0xfa; 0x2e; 0xa0; 0x8a; 0xec; 0x35; 0xd9; 0x81; 0x54; 0xc5; 0x2f; 0x31;
     0x5d; 0x4a; 0x71; 0x26; 0x70; 0xa2; 0x7e; 0xc4; 0xe5; 0xe3; 0xa0; 0x96; 0xf2; 0xe1; 0x0a; 0xa6;
     0x23; 0x90; 0x66; 0x40; 0x42; 0xc7; 0xb6; 0xb8; 0x2f; 0x24; 0x79; 0x70; 0xc6; 0x74; 0xf0; 0xca;
     0x79; 0x57; 0xb9; 0xe0; 0xf3; 0x0b; 0x23; 0x39; 0x07; 0x71; 0xee; 0x4a; 0x67; 0xd9; 0x1b; 0x30;
     0x39; 0xc6; 0x45; 0xee; 0x63; 0x7f; 0x50; 0x84; 0x20; 0x2d; 0x5b; 0x03; 0x03; 0xd5; 0x46; 0x6d;
     0x92; 0x72; 0xc5; 0xd7; 0x73; 0x36; 0x8a; 0xbc; 0x06; 0x84; 0xd6; 0xbc; 0xc1; 0x9d; 0x30; 0x27;
     0x73; 0x24; 0x54; 0x3e; 0xcd; 0xaf; 0x56; 0xf7; 0x44; 0x6e; 0x20; 0x79; 0xb8; 0x9c; 0xc4; 0x8f;
     0x2d])
  in
  assert_norm (List.Tot.length l == 129);
  createL_global l

//
// Test3
//
let test3_n: b:ilbuffer uint8 192ul{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8
    [0xe6; 0xbd; 0x69; 0x2a; 0xc9; 0x66; 0x45; 0x79; 0x04; 0x03; 0xfd; 0xd0; 0xf5; 0xbe; 0xb8; 0xb9;
     0xbf; 0x92; 0xed; 0x10; 0x00; 0x7f; 0xc3; 0x65; 0x04; 0x64; 0x19; 0xdd; 0x06; 0xc0; 0x5c; 0x5b;
     0x5b; 0x2f; 0x48; 0xec; 0xf9; 0x89; 0xe4; 0xce; 0x26; 0x91; 0x09; 0x97; 0x9c; 0xbb; 0x40; 0xb4;
     0xa0; 0xad; 0x24; 0xd2; 0x24; 0x83; 0xd1; 0xee; 0x31; 0x5a; 0xd4; 0xcc; 0xb1; 0x53; 0x42; 0x68;
     0x35; 0x26; 0x91; 0xc5; 0x24; 0xf6; 0xdd; 0x8e; 0x6c; 0x29; 0xd2; 0x24; 0xcf; 0x24; 0x69; 0x73;
     0xae; 0xc8; 0x6c; 0x5b; 0xf6; 0xb1; 0x40; 0x1a; 0x85; 0x0d; 0x1b; 0x9a; 0xd1; 0xbb; 0x8c; 0xbc;
     0xec; 0x47; 0xb0; 0x6f; 0x0f; 0x8c; 0x7f; 0x45; 0xd3; 0xfc; 0x8f; 0x31; 0x92; 0x99; 0xc5; 0x43;
     0x3d; 0xdb; 0xc2; 0xb3; 0x05; 0x3b; 0x47; 0xde; 0xd2; 0xec; 0xd4; 0xa4; 0xca; 0xef; 0xd6; 0x14;
     0x83; 0x3d; 0xc8; 0xbb; 0x62; 0x2f; 0x31; 0x7e; 0xd0; 0x76; 0xb8; 0x05; 0x7f; 0xe8; 0xde; 0x3f;
     0x84; 0x48; 0x0a; 0xd5; 0xe8; 0x3e; 0x4a; 0x61; 0x90; 0x4a; 0x4f; 0x24; 0x8f; 0xb3; 0x97; 0x02;
     0x73; 0x57; 0xe1; 0xd3; 0x0e; 0x46; 0x31; 0x39; 0x81; 0x5c; 0x6f; 0xd4; 0xfd; 0x5a; 0xc5; 0xb8;
     0x17; 0x2a; 0x45; 0x23; 0x0e; 0xcb; 0x63; 0x18; 0xa0; 0x4f; 0x14; 0x55; 0xd8; 0x4e; 0x5a; 0x8b])
  in
  assert_norm (List.Tot.length l == 192);
  createL_global l

let test3_e: b:ilbuffer uint8 3ul{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [0x01; 0x00; 0x01]) in
  assert_norm (List.Tot.length l == 3);
  createL_global l

let test3_d: b:ilbuffer uint8 192ul{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8
    [0x6a; 0x7f; 0xd8; 0x4f; 0xb8; 0x5f; 0xad; 0x07; 0x3b; 0x34; 0x40; 0x6d; 0xb7; 0x4f; 0x8d; 0x61;
     0xa6; 0xab; 0xc1; 0x21; 0x96; 0xa9; 0x61; 0xdd; 0x79; 0x56; 0x5e; 0x9d; 0xa6; 0xe5; 0x18; 0x7b;
     0xce; 0x2d; 0x98; 0x02; 0x50; 0xf7; 0x35; 0x95; 0x75; 0x35; 0x92; 0x70; 0xd9; 0x15; 0x90; 0xbb;
     0x0e; 0x42; 0x7c; 0x71; 0x46; 0x0b; 0x55; 0xd5; 0x14; 0x10; 0xb1; 0x91; 0xbc; 0xf3; 0x09; 0xfe;
     0xa1; 0x31; 0xa9; 0x2c; 0x8e; 0x70; 0x27; 0x38; 0xfa; 0x71; 0x9f; 0x1e; 0x00; 0x41; 0xf5; 0x2e;
     0x40; 0xe9; 0x1f; 0x22; 0x9f; 0x4d; 0x96; 0xa1; 0xe6; 0xf1; 0x72; 0xe1; 0x55; 0x96; 0xb4; 0x51;
     0x0a; 0x6d; 0xae; 0xc2; 0x61; 0x05; 0xf2; 0xbe; 0xbc; 0x53; 0x31; 0x6b; 0x87; 0xbd; 0xf2; 0x13;
     0x11; 0x66; 0x60; 0x70; 0xe8; 0xdf; 0xee; 0x69; 0xd5; 0x2c; 0x71; 0xa9; 0x76; 0xca; 0xae; 0x79;
     0xc7; 0x2b; 0x68; 0xd2; 0x85; 0x80; 0xdc; 0x68; 0x6d; 0x9f; 0x51; 0x29; 0xd2; 0x25; 0xf8; 0x2b;
     0x3d; 0x61; 0x55; 0x13; 0xa8; 0x82; 0xb3; 0xdb; 0x91; 0x41; 0x6b; 0x48; 0xce; 0x08; 0x88; 0x82;
     0x13; 0xe3; 0x7e; 0xeb; 0x9a; 0xf8; 0x00; 0xd8; 0x1c; 0xab; 0x32; 0x8c; 0xe4; 0x20; 0x68; 0x99;
     0x03; 0xc0; 0x0c; 0x7b; 0x5f; 0xd3; 0x1b; 0x75; 0x50; 0x3a; 0x6d; 0x41; 0x96; 0x84; 0xd6; 0x29])
  in
  assert_norm (List.Tot.length l == 192);
  createL_global l

let test3_p: b:ilbuffer uint8 96ul{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8
    [0xf8; 0xeb; 0x97; 0xe9; 0x8d; 0xf1; 0x26; 0x64; 0xee; 0xfd; 0xb7; 0x61; 0x59; 0x6a; 0x69; 0xdd;
     0xcd; 0x0e; 0x76; 0xda; 0xec; 0xe6; 0xed; 0x4b; 0xf5; 0xa1; 0xb5; 0x0a; 0xc0; 0x86; 0xf7; 0x92;
     0x8a; 0x4d; 0x2f; 0x87; 0x26; 0xa7; 0x7e; 0x51; 0x5b; 0x74; 0xda; 0x41; 0x98; 0x8f; 0x22; 0x0b;
     0x1c; 0xc8; 0x7a; 0xa1; 0xfc; 0x81; 0x0c; 0xe9; 0x9a; 0x82; 0xf2; 0xd1; 0xce; 0x82; 0x1e; 0xdc;
     0xed; 0x79; 0x4c; 0x69; 0x41; 0xf4; 0x2c; 0x7a; 0x1a; 0x0b; 0x8c; 0x4d; 0x28; 0xc7; 0x5e; 0xc6;
     0x0b; 0x65; 0x22; 0x79; 0xf6; 0x15; 0x4a; 0x76; 0x2a; 0xed; 0x16; 0x5d; 0x47; 0xde; 0xe3; 0x67])
  in
  assert_norm (List.Tot.length l == 96);
  createL_global l

let test3_q: b:ilbuffer uint8 96ul{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8
    [0xed; 0x4d; 0x71; 0xd0; 0xa6; 0xe2; 0x4b; 0x93; 0xc2; 0xe5; 0xf6; 0xb4; 0xbb; 0xe0; 0x5f; 0x5f;
     0xb0; 0xaf; 0xa0; 0x42; 0xd2; 0x04; 0xfe; 0x33; 0x78; 0xd3; 0x65; 0xc2; 0xf2; 0x88; 0xb6; 0xa8;
     0xda; 0xd7; 0xef; 0xe4; 0x5d; 0x15; 0x3e; 0xef; 0x40; 0xca; 0xcc; 0x7b; 0x81; 0xff; 0x93; 0x40;
     0x02; 0xd1; 0x08; 0x99; 0x4b; 0x94; 0xa5; 0xe4; 0x72; 0x8c; 0xd9; 0xc9; 0x63; 0x37; 0x5a; 0xe4;
     0x99; 0x65; 0xbd; 0xa5; 0x5c; 0xbf; 0x0e; 0xfe; 0xd8; 0xd6; 0x55; 0x3b; 0x40; 0x27; 0xf2; 0xd8;
     0x62; 0x08; 0xa6; 0xe6; 0xb4; 0x89; 0xc1; 0x76; 0x12; 0x80; 0x92; 0xd6; 0x29; 0xe4; 0x9d; 0x3d])
  in
  assert_norm (List.Tot.length l == 96);
  createL_global l

let test3_r2: b:ilbuffer uint8 192ul{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8
    [0xab; 0xe0; 0x23; 0x26; 0xa2; 0x05; 0x6c; 0x70; 0xc2; 0xf0; 0xbd; 0x07; 0x26; 0x75; 0xc4; 0xce;
     0xb4; 0x43; 0xd8; 0xb5; 0xf1; 0x7a; 0xa8; 0x56; 0xa0; 0x4e; 0x01; 0x7f; 0x85; 0x32; 0xb3; 0xd5;
     0x35; 0x9b; 0x34; 0x30; 0x2d; 0xad; 0x42; 0x52; 0xf3; 0x05; 0x2c; 0x90; 0x52; 0x5d; 0xcf; 0xce;
     0x88; 0x73; 0x82; 0x81; 0x92; 0x2b; 0x64; 0xca; 0x69; 0x1c; 0x63; 0x2f; 0x75; 0xe1; 0xe3; 0xbb;
     0x33; 0xaf; 0x08; 0x54; 0xa3; 0x58; 0xb0; 0x1f; 0xca; 0x4c; 0xc4; 0xbc; 0x3c; 0x5a; 0xa6; 0x86;
     0xc3; 0xf9; 0x50; 0x55; 0xee; 0x44; 0x4b; 0x45; 0x62; 0xb3; 0x60; 0x86; 0xc5; 0x24; 0x2e; 0x34;
     0x7e; 0xa6; 0x20; 0x98; 0xb1; 0x4e; 0x75; 0x49; 0xf6; 0x02; 0x6c; 0x01; 0xce; 0x5c; 0x0b; 0x79;
     0x11; 0x1c; 0x9e; 0x7d; 0x9b; 0xe6; 0x55; 0x5b; 0xf1; 0xa8; 0xc4; 0xd5; 0x01; 0xbb; 0xd9; 0xbc;
     0x74; 0xbd; 0xf8; 0x14; 0x8c; 0xe7; 0x7b; 0x95; 0x2e; 0x7b; 0x17; 0x7d; 0x68; 0x91; 0x29; 0xd7;
     0x3c; 0xca; 0xab; 0x47; 0x15; 0xee; 0xd1; 0x72; 0x04; 0x70; 0xbf; 0x2e; 0x39; 0x5f; 0x95; 0x64;
     0xfd; 0xcc; 0xdd; 0x50; 0x29; 0x14; 0x28; 0xa2; 0xb9; 0xb5; 0xa9; 0x43; 0xd3; 0xd4; 0x3b; 0xdf;
     0xd5; 0x17; 0x2b; 0x92; 0xfe; 0xdb; 0x1c; 0x55; 0xad; 0x90; 0xca; 0x81; 0xf4; 0x24; 0x48; 0xe3])
  in
  assert_norm (List.Tot.length l == 192);
  createL_global l

let test3_rBlind: b:ilbuffer uint8 8ul{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8
    [0x35; 0x26; 0x91; 0xc5; 0x24; 0xf6; 0xdd; 0x8e])
  in
  assert_norm (List.Tot.length l == 8);
  createL_global l

let test3_msg: b:ilbuffer uint8 107ul{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8
    [0xc8; 0xc9; 0xc6; 0xaf; 0x04; 0xac; 0xda; 0x41; 0x4d; 0x22; 0x7e; 0xf2; 0x3e; 0x08; 0x20; 0xc3;
     0x73; 0x2c; 0x50; 0x0d; 0xc8; 0x72; 0x75; 0xe9; 0x5b; 0x0d; 0x09; 0x54; 0x13; 0x99; 0x3c; 0x26;
     0x58; 0xbc; 0x1d; 0x98; 0x85; 0x81; 0xba; 0x87; 0x9c; 0x2d; 0x20; 0x1f; 0x14; 0xcb; 0x88; 0xce;
     0xd1; 0x53; 0xa0; 0x19; 0x69; 0xa7; 0xbf; 0x0a; 0x7b; 0xe7; 0x9c; 0x84; 0xc1; 0x48; 0x6b; 0xc1;
     0x2b; 0x3f; 0xa6; 0xc5; 0x98; 0x71; 0xb6; 0x82; 0x7c; 0x8c; 0xe2; 0x53; 0xca; 0x5f; 0xef; 0xa8;
     0xa8; 0xc6; 0x90; 0xbf; 0x32; 0x6e; 0x8e; 0x37; 0xcd; 0xb9; 0x6d; 0x90; 0xa8; 0x2e; 0xba; 0xb6;
     0x9f; 0x86; 0x35; 0x0e; 0x18; 0x22; 0xe8; 0xbd; 0x53; 0x6a; 0x2e])
  in
  assert_norm (List.Tot.length l == 107);
  createL_global l

let test3_salt: b:ilbuffer uint8 20ul{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8
    [0xb3; 0x07; 0xc4; 0x3b; 0x48; 0x50; 0xa8; 0xda; 0xc2; 0xf1; 0x5f; 0x32; 0xe3; 0x78; 0x39; 0xef;
     0x8c; 0x5c; 0x0e; 0x91])
  in
  assert_norm (List.Tot.length l == 20);
  createL_global l

let test3_sgnt_expected: b:ilbuffer uint8 192ul{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8
    [0x0c; 0x58; 0xaa; 0x0a; 0x5d; 0xe6; 0xd8; 0xa0; 0x0b; 0xb6; 0xac; 0x2d; 0x5c; 0x04; 0xfb; 0x0f;
     0xa3; 0x01; 0x12; 0x49; 0x3b; 0xde; 0x42; 0x28; 0x8a; 0x5b; 0xad; 0x5c; 0x7b; 0x4b; 0x51; 0x8e;
     0x21; 0xf3; 0x1c; 0x18; 0x54; 0x71; 0xb5; 0x9f; 0x87; 0x33; 0xc1; 0x3f; 0xe4; 0xc7; 0xfe; 0xc4;
     0xa2; 0x4d; 0x0d; 0x0c; 0xd6; 0x62; 0xec; 0xd5; 0xe7; 0x21; 0xb0; 0x53; 0x62; 0xd9; 0xb6; 0x72;
     0xa3; 0xd8; 0x26; 0x82; 0x55; 0x2c; 0x58; 0x30; 0x0d; 0xa6; 0x14; 0x65; 0x66; 0x38; 0xe6; 0x61;
     0x83; 0x9d; 0x33; 0xb4; 0xd3; 0xd3; 0x7e; 0x0f; 0xce; 0x8b; 0xa0; 0xe4; 0x93; 0xd0; 0x2b; 0xc4;
     0x73; 0xf8; 0x53; 0x78; 0x71; 0xbb; 0x56; 0x55; 0xc6; 0x94; 0x07; 0xb3; 0x62; 0xe0; 0x73; 0x90;
     0x07; 0xe0; 0x36; 0x7a; 0x39; 0xc0; 0x38; 0xce; 0xd3; 0x7f; 0xf4; 0xfb; 0x9f; 0x16; 0x0d; 0x4d;
     0x06; 0x39; 0x62; 0x17; 0x31; 0x5e; 0xe8; 0xd7; 0x5d; 0x91; 0x0b; 0x51; 0x28; 0x45; 0xf9; 0x70;
     0xfe; 0x74; 0xe4; 0x12; 0x26; 0x84; 0x71; 0xc9; 0x51; 0x81; 0x62; 0x51; 0x6c; 0xd6; 0xf9; 0x66;
     0x89; 0x2a; 0x74; 0x0e; 0x1b; 0x8a; 0x88; 0x76; 0x6a; 0x30; 0xfc; 0xe9; 0xb6; 0x0e; 0x03; 0x32;
     0xd7; 0xa0; 0x1b; 0xa5; 0xfa; 0x13; 0x5f; 0xe7; 0xc4; 0x92; 0x72; 0xac; 0xbb; 0x1d; 0x30; 0xf1])
  in
  assert_norm (List.Tot.length l == 192);
  createL_global l


//
// Test4
//
let test4_n: b:ilbuffer uint8 256ul{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8
    [0xa5; 0xdd; 0x86; 0x7a; 0xc4; 0xcb; 0x02; 0xf9; 0x0b; 0x94; 0x57; 0xd4; 0x8c; 0x14; 0xa7; 0x70;
     0xef; 0x99; 0x1c; 0x56; 0xc3; 0x9c; 0x0e; 0xc6; 0x5f; 0xd1; 0x1a; 0xfa; 0x89; 0x37; 0xce; 0xa5;
     0x7b; 0x9b; 0xe7; 0xac; 0x73; 0xb4; 0x5c; 0x00; 0x17; 0x61; 0x5b; 0x82; 0xd6; 0x22; 0xe3; 0x18;
     0x75; 0x3b; 0x60; 0x27; 0xc0; 0xfd; 0x15; 0x7b; 0xe1; 0x2f; 0x80; 0x90; 0xfe; 0xe2; 0xa7; 0xad;
     0xcd; 0x0e; 0xef; 0x75; 0x9f; 0x88; 0xba; 0x49; 0x97; 0xc7; 0xa4; 0x2d; 0x58; 0xc9; 0xaa; 0x12;
     0xcb; 0x99; 0xae; 0x00; 0x1f; 0xe5; 0x21; 0xc1; 0x3b; 0xb5; 0x43; 0x14; 0x45; 0xa8; 0xd5; 0xae;
     0x4f; 0x5e; 0x4c; 0x7e; 0x94; 0x8a; 0xc2; 0x27; 0xd3; 0x60; 0x40; 0x71; 0xf2; 0x0e; 0x57; 0x7e;
     0x90; 0x5f; 0xbe; 0xb1; 0x5d; 0xfa; 0xf0; 0x6d; 0x1d; 0xe5; 0xae; 0x62; 0x53; 0xd6; 0x3a; 0x6a;
     0x21; 0x20; 0xb3; 0x1a; 0x5d; 0xa5; 0xda; 0xbc; 0x95; 0x50; 0x60; 0x0e; 0x20; 0xf2; 0x7d; 0x37;
     0x39; 0xe2; 0x62; 0x79; 0x25; 0xfe; 0xa3; 0xcc; 0x50; 0x9f; 0x21; 0xdf; 0xf0; 0x4e; 0x6e; 0xea;
     0x45; 0x49; 0xc5; 0x40; 0xd6; 0x80; 0x9f; 0xf9; 0x30; 0x7e; 0xed; 0xe9; 0x1f; 0xff; 0x58; 0x73;
     0x3d; 0x83; 0x85; 0xa2; 0x37; 0xd6; 0xd3; 0x70; 0x5a; 0x33; 0xe3; 0x91; 0x90; 0x09; 0x92; 0x07;
     0x0d; 0xf7; 0xad; 0xf1; 0x35; 0x7c; 0xf7; 0xe3; 0x70; 0x0c; 0xe3; 0x66; 0x7d; 0xe8; 0x3f; 0x17;
     0xb8; 0xdf; 0x17; 0x78; 0xdb; 0x38; 0x1d; 0xce; 0x09; 0xcb; 0x4a; 0xd0; 0x58; 0xa5; 0x11; 0x00;
     0x1a; 0x73; 0x81; 0x98; 0xee; 0x27; 0xcf; 0x55; 0xa1; 0x3b; 0x75; 0x45; 0x39; 0x90; 0x65; 0x82;
     0xec; 0x8b; 0x17; 0x4b; 0xd5; 0x8d; 0x5d; 0x1f; 0x3d; 0x76; 0x7c; 0x61; 0x37; 0x21; 0xae; 0x05])
  in
  assert_norm (List.Tot.length l == 256);
  createL_global l

let test4_e: b:ilbuffer uint8 3ul{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [0x01; 0x00; 0x01]) in
  assert_norm (List.Tot.length l == 3);
  createL_global l

let test4_d: b:ilbuffer uint8 256ul{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8
    [0x2d; 0x2f; 0xf5; 0x67; 0xb3; 0xfe; 0x74; 0xe0; 0x61; 0x91; 0xb7; 0xfd; 0xed; 0x6d; 0xe1; 0x12;
     0x29; 0x0c; 0x67; 0x06; 0x92; 0x43; 0x0d; 0x59; 0x69; 0x18; 0x40; 0x47; 0xda; 0x23; 0x4c; 0x96;
     0x93; 0xde; 0xed; 0x16; 0x73; 0xed; 0x42; 0x95; 0x39; 0xc9; 0x69; 0xd3; 0x72; 0xc0; 0x4d; 0x6b;
     0x47; 0xe0; 0xf5; 0xb8; 0xce; 0xe0; 0x84; 0x3e; 0x5c; 0x22; 0x83; 0x5d; 0xbd; 0x3b; 0x05; 0xa0;
     0x99; 0x79; 0x84; 0xae; 0x60; 0x58; 0xb1; 0x1b; 0xc4; 0x90; 0x7c; 0xbf; 0x67; 0xed; 0x84; 0xfa;
     0x9a; 0xe2; 0x52; 0xdf; 0xb0; 0xd0; 0xcd; 0x49; 0xe6; 0x18; 0xe3; 0x5d; 0xfd; 0xfe; 0x59; 0xbc;
     0xa3; 0xdd; 0xd6; 0x6c; 0x33; 0xce; 0xbb; 0xc7; 0x7a; 0xd4; 0x41; 0xaa; 0x69; 0x5e; 0x13; 0xe3;
     0x24; 0xb5; 0x18; 0xf0; 0x1c; 0x60; 0xf5; 0xa8; 0x5c; 0x99; 0x4a; 0xd1; 0x79; 0xf2; 0xa6; 0xb5;
     0xfb; 0xe9; 0x34; 0x02; 0xb1; 0x17; 0x67; 0xbe; 0x01; 0xbf; 0x07; 0x34; 0x44; 0xd6; 0xba; 0x1d;
     0xd2; 0xbc; 0xa5; 0xbd; 0x07; 0x4d; 0x4a; 0x5f; 0xae; 0x35; 0x31; 0xad; 0x13; 0x03; 0xd8; 0x4b;
     0x30; 0xd8; 0x97; 0x31; 0x8c; 0xbb; 0xba; 0x04; 0xe0; 0x3c; 0x2e; 0x66; 0xde; 0x6d; 0x91; 0xf8;
     0x2f; 0x96; 0xea; 0x1d; 0x4b; 0xb5; 0x4a; 0x5a; 0xae; 0x10; 0x2d; 0x59; 0x46; 0x57; 0xf5; 0xc9;
     0x78; 0x95; 0x53; 0x51; 0x2b; 0x29; 0x6d; 0xea; 0x29; 0xd8; 0x02; 0x31; 0x96; 0x35; 0x7e; 0x3e;
     0x3a; 0x6e; 0x95; 0x8f; 0x39; 0xe3; 0xc2; 0x34; 0x40; 0x38; 0xea; 0x60; 0x4b; 0x31; 0xed; 0xc6;
     0xf0; 0xf7; 0xff; 0x6e; 0x71; 0x81; 0xa5; 0x7c; 0x92; 0x82; 0x6a; 0x26; 0x8f; 0x86; 0x76; 0x8e;
     0x96; 0xf8; 0x78; 0x56; 0x2f; 0xc7; 0x1d; 0x85; 0xd6; 0x9e; 0x44; 0x86; 0x12; 0xf7; 0x04; 0x8f])
  in
  assert_norm (List.Tot.length l == 256);
  createL_global l

let test4_p: b:ilbuffer uint8 128ul{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8
    [0xcf; 0xd5; 0x02; 0x83; 0xfe; 0xee; 0xb9; 0x7f; 0x6f; 0x08; 0xd7; 0x3c; 0xbc; 0x7b; 0x38; 0x36;
     0xf8; 0x2b; 0xbc; 0xd4; 0x99; 0x47; 0x9f; 0x5e; 0x6f; 0x76; 0xfd; 0xfc; 0xb8; 0xb3; 0x8c; 0x4f;
     0x71; 0xdc; 0x9e; 0x88; 0xbd; 0x6a; 0x6f; 0x76; 0x37; 0x1a; 0xfd; 0x65; 0xd2; 0xaf; 0x18; 0x62;
     0xb3; 0x2a; 0xfb; 0x34; 0xa9; 0x5f; 0x71; 0xb8; 0xb1; 0x32; 0x04; 0x3f; 0xfe; 0xbe; 0x3a; 0x95;
     0x2b; 0xaf; 0x75; 0x92; 0x44; 0x81; 0x48; 0xc0; 0x3f; 0x9c; 0x69; 0xb1; 0xd6; 0x8e; 0x4c; 0xe5;
     0xcf; 0x32; 0xc8; 0x6b; 0xaf; 0x46; 0xfe; 0xd3; 0x01; 0xca; 0x1a; 0xb4; 0x03; 0x06; 0x9b; 0x32;
     0xf4; 0x56; 0xb9; 0x1f; 0x71; 0x89; 0x8a; 0xb0; 0x81; 0xcd; 0x8c; 0x42; 0x52; 0xef; 0x52; 0x71;
     0x91; 0x5c; 0x97; 0x94; 0xb8; 0xf2; 0x95; 0x85; 0x1d; 0xa7; 0x51; 0x0f; 0x99; 0xcb; 0x73; 0xeb])
  in
  assert_norm (List.Tot.length l == 128);
  createL_global l

let test4_q: b:ilbuffer uint8 128ul{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8
    [0xcc; 0x4e; 0x90; 0xd2; 0xa1; 0xb3; 0xa0; 0x65; 0xd3; 0xb2; 0xd1; 0xf5; 0xa8; 0xfc; 0xe3; 0x1b;
     0x54; 0x44; 0x75; 0x66; 0x4e; 0xab; 0x56; 0x1d; 0x29; 0x71; 0xb9; 0x9f; 0xb7; 0xbe; 0xf8; 0x44;
     0xe8; 0xec; 0x1f; 0x36; 0x0b; 0x8c; 0x2a; 0xc8; 0x35; 0x96; 0x92; 0x97; 0x1e; 0xa6; 0xa3; 0x8f;
     0x72; 0x3f; 0xcc; 0x21; 0x1f; 0x5d; 0xbc; 0xb1; 0x77; 0xa0; 0xfd; 0xac; 0x51; 0x64; 0xa1; 0xd4;
     0xff; 0x7f; 0xbb; 0x4e; 0x82; 0x99; 0x86; 0x35; 0x3c; 0xb9; 0x83; 0x65; 0x9a; 0x14; 0x8c; 0xdd;
     0x42; 0x0c; 0x7d; 0x31; 0xba; 0x38; 0x22; 0xea; 0x90; 0xa3; 0x2b; 0xe4; 0x6c; 0x03; 0x0e; 0x8c;
     0x17; 0xe1; 0xfa; 0x0a; 0xd3; 0x78; 0x59; 0xe0; 0x6b; 0x0a; 0xa6; 0xfa; 0x3b; 0x21; 0x6d; 0x9c;
     0xbe; 0x6c; 0x0e; 0x22; 0x33; 0x97; 0x69; 0xc0; 0xa6; 0x15; 0x91; 0x3e; 0x5d; 0xa7; 0x19; 0xcf])
  in
  assert_norm (List.Tot.length l == 128);
  createL_global l

let test4_r2: b:ilbuffer uint8 256ul{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8
    [0x4a; 0x68; 0x36; 0x42; 0xc4; 0x4f; 0xc2; 0xfb; 0xb0; 0xc4; 0x5d; 0x16; 0x47; 0x7b; 0x79; 0xb5;
     0xdd; 0x61; 0x50; 0x21; 0x66; 0xc1; 0x13; 0x7f; 0x43; 0x68; 0xd0; 0x68; 0x34; 0x4a; 0x2c; 0xf3;
     0xdd; 0x80; 0x22; 0xe6; 0xcc; 0xf1; 0x12; 0x7e; 0x69; 0x13; 0x64; 0x28; 0x5c; 0x61; 0x29; 0x51;
     0xee; 0x95; 0x5f; 0x63; 0xcf; 0x62; 0x70; 0x00; 0x20; 0xc3; 0xc8; 0xdf; 0x9d; 0x52; 0x2d; 0x50;
     0x14; 0x7a; 0x25; 0x01; 0x1b; 0x70; 0xf1; 0xb9; 0xf0; 0x09; 0x89; 0xef; 0x90; 0xd7; 0x7d; 0xe0;
     0x48; 0xb0; 0xff; 0x02; 0xd8; 0x9d; 0x74; 0x7e; 0xfa; 0x4c; 0x61; 0x3d; 0x1d; 0x71; 0xf1; 0xf6;
     0xc8; 0xcc; 0xbe; 0xdb; 0xdd; 0xd4; 0xdb; 0x01; 0x46; 0x83; 0xff; 0xcd; 0x88; 0x90; 0x98; 0xf5;
     0x58; 0x50; 0x65; 0x6c; 0x62; 0xf7; 0x40; 0x36; 0xe9; 0xd9; 0x33; 0x1e; 0x0f; 0x32; 0x3e; 0xde;
     0xf3; 0x99; 0xdd; 0x8b; 0x68; 0xb5; 0x4b; 0x9a; 0xf6; 0xdd; 0x91; 0x17; 0xa4; 0xd6; 0xbc; 0x34;
     0xa0; 0x74; 0x6d; 0x7e; 0x55; 0xc1; 0x14; 0xac; 0x0d; 0x48; 0xe8; 0xe0; 0x4b; 0x32; 0x63; 0xdd;
     0x45; 0xe5; 0x41; 0xa1; 0x9a; 0x88; 0xf0; 0xab; 0xa6; 0xe6; 0x07; 0x3a; 0xdb; 0xb0; 0x33; 0xc7;
     0x69; 0xee; 0x2a; 0xab; 0x4d; 0x0e; 0x5a; 0x7e; 0x80; 0x9e; 0xca; 0x81; 0xc3; 0xa7; 0x43; 0xd9;
     0xfb; 0x57; 0x11; 0xff; 0x19; 0xc6; 0x62; 0xe9; 0x91; 0x6e; 0xc5; 0x94; 0xd3; 0xf1; 0x37; 0x09;
     0x88; 0x13; 0x65; 0xd2; 0x5d; 0x50; 0x62; 0xf3; 0x20; 0xb6; 0x1b; 0x27; 0xd2; 0xaf; 0x64; 0x2b;
     0x56; 0x79; 0xdb; 0x11; 0x56; 0xd3; 0xba; 0x95; 0xff; 0x52; 0x93; 0xfe; 0x80; 0x9a; 0xfd; 0x8d;
     0xff; 0x5a; 0x1a; 0x8c; 0x92; 0x84; 0xbf; 0x76; 0x80; 0x00; 0x72; 0xb5; 0x74; 0x3b; 0x9c; 0x72])
  in
  assert_norm (List.Tot.length l == 256);
  createL_global l

let test4_rBlind: b:ilbuffer uint8 8ul{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8
    [0x7b; 0x9b; 0xe7; 0xac; 0x73; 0xb4; 0x5c; 0x00])
  in
  assert_norm (List.Tot.length l == 8);
  createL_global l

let test4_msg: b:ilbuffer uint8 128ul{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8
    [0xdd; 0x67; 0x0a; 0x01; 0x46; 0x58; 0x68; 0xad; 0xc9; 0x3f; 0x26; 0x13; 0x19; 0x57; 0xa5; 0x0c;
     0x52; 0xfb; 0x77; 0x7c; 0xdb; 0xaa; 0x30; 0x89; 0x2c; 0x9e; 0x12; 0x36; 0x11; 0x64; 0xec; 0x13;
     0x97; 0x9d; 0x43; 0x04; 0x81; 0x18; 0xe4; 0x44; 0x5d; 0xb8; 0x7b; 0xee; 0x58; 0xdd; 0x98; 0x7b;
     0x34; 0x25; 0xd0; 0x20; 0x71; 0xd8; 0xdb; 0xae; 0x80; 0x70; 0x8b; 0x03; 0x9d; 0xbb; 0x64; 0xdb;
     0xd1; 0xde; 0x56; 0x57; 0xd9; 0xfe; 0xd0; 0xc1; 0x18; 0xa5; 0x41; 0x43; 0x74; 0x2e; 0x0f; 0xf3;
     0xc8; 0x7f; 0x74; 0xe4; 0x58; 0x57; 0x64; 0x7a; 0xf3; 0xf7; 0x9e; 0xb0; 0xa1; 0x4c; 0x9d; 0x75;
     0xea; 0x9a; 0x1a; 0x04; 0xb7; 0xcf; 0x47; 0x8a; 0x89; 0x7a; 0x70; 0x8f; 0xd9; 0x88; 0xf4; 0x8e;
     0x80; 0x1e; 0xdb; 0x0b; 0x70; 0x39; 0xdf; 0x8c; 0x23; 0xbb; 0x3c; 0x56; 0xf4; 0xe8; 0x21; 0xac])
  in
  assert_norm (List.Tot.length l == 128);
  createL_global l

let test4_salt: b:ilbuffer uint8 20ul{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8
    [0x8b; 0x2b; 0xdd; 0x4b; 0x40; 0xfa; 0xf5; 0x45; 0xc7; 0x78; 0xdd; 0xf9; 0xbc; 0x1a; 0x49; 0xcb;
     0x57; 0xf9; 0xb7; 0x1b])
  in
  assert_norm (List.Tot.length l == 20);
  createL_global l

let test4_sgnt_expected: b:ilbuffer uint8 256ul{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8
    [0xa4; 0x4e; 0x5c; 0x83; 0xc6; 0xfe; 0xdf; 0x7f; 0x44; 0x33; 0x78; 0x82; 0x54; 0x2a; 0x96; 0x10;
     0x72; 0x4a; 0xa6; 0xf5; 0xb8; 0xf1; 0x3b; 0x4f; 0x51; 0xeb; 0x9e; 0xf9; 0x84; 0xf5; 0x19; 0xaa;
     0xe9; 0xe3; 0x4b; 0x26; 0x4e; 0x8d; 0x06; 0xb6; 0x93; 0x66; 0x4d; 0xe1; 0xcc; 0xe1; 0x36; 0xd0;
     0x6d; 0x10; 0x7f; 0x64; 0x51; 0x99; 0x8a; 0xf9; 0x01; 0x21; 0x3f; 0xc8; 0x95; 0x83; 0xe6; 0xbe;
     0xfe; 0x1e; 0xd1; 0x12; 0x35; 0xf5; 0xb5; 0xce; 0x8b; 0xd4; 0x72; 0xb3; 0x84; 0xef; 0xf0; 0xcd;
     0x80; 0xd3; 0x75; 0xbd; 0x6a; 0x88; 0xae; 0x6f; 0x5b; 0x76; 0x75; 0xc2; 0x50; 0x8b; 0xa9; 0xb9;
     0xf0; 0x17; 0x1e; 0x10; 0xc9; 0x58; 0xd4; 0xc0; 0x4c; 0x10; 0x0e; 0xf9; 0x06; 0xcc; 0x97; 0x58;
     0x0d; 0xe7; 0x73; 0xad; 0x9d; 0xf4; 0xda; 0x13; 0xd5; 0x95; 0xbe; 0xe2; 0x4a; 0xf8; 0x12; 0x88;
     0x4e; 0xd4; 0xdc; 0xe8; 0x09; 0x51; 0xec; 0xd0; 0x4b; 0x1b; 0xa6; 0xd7; 0x8c; 0x29; 0x34; 0xe6;
     0xab; 0x0a; 0x77; 0x36; 0x83; 0x91; 0x1f; 0xcc; 0x68; 0x91; 0x35; 0x37; 0x67; 0x27; 0x78; 0x09;
     0xec; 0x74; 0x6f; 0x95; 0x98; 0xe4; 0xf8; 0xf0; 0xcb; 0x1d; 0x3d; 0x37; 0x84; 0x3f; 0xea; 0x2a;
     0x8c; 0xb0; 0x91; 0xf2; 0x91; 0x91; 0x22; 0x76; 0x9e; 0xe4; 0x17; 0xda; 0x18; 0xd6; 0x03; 0xf7;
     0x98; 0x37; 0x0c; 0xad; 0x7b; 0x76; 0x0a; 0x7f; 0x57; 0x3a; 0xea; 0xf5; 0x16; 0xa0; 0xf9; 0x0d;
     0x95; 0x25; 0x65; 0xb8; 0xa1; 0x9a; 0x8f; 0xc3; 0xf0; 0xee; 0x7d; 0x39; 0x1d; 0x9b; 0x8b; 0x3f;
     0x98; 0xbe; 0xbb; 0x0d; 0x5d; 0x01; 0x0e; 0x32; 0xe0; 0xb8; 0x00; 0xe9; 0x65; 0x6f; 0x64; 0x08;
     0x2b; 0xb1; 0xac; 0x95; 0xa2; 0x23; 0xf4; 0x31; 0xec; 0x40; 0x6a; 0x42; 0x95; 0x4b; 0x2d; 0x57])
  in
  assert_norm (List.Tot.length l == 256);
  createL_global l

val main: unit -> St C.exit_code
let main () =
  admit();
  let test1 =
    ctest 16ul 1024ul test1_n 24ul test1_e 1024ul test1_d 64ul test1_p 64ul test1_q
    test1_r2 8ul test1_rBlind 51ul test1_msg 20ul test1_salt test1_sgnt_expected in
  let test2 =
    ctest 32ul 1025ul test2_n 24ul test2_e 1024ul test2_d 65ul test2_p 65ul test2_q
    test2_r2 8ul test2_rBlind 234ul test2_msg 20ul test2_salt test2_sgnt_expected in
  let test3 =
    ctest 32ul 1536ul test3_n 24ul test3_e 1536ul test3_d 96ul test3_p 96ul test3_q
    test3_r2 8ul test3_rBlind 107ul test3_msg 20ul test3_salt test3_sgnt_expected in
  let test4 =
    ctest 32ul 2048ul test4_n 24ul test4_e 2048ul test4_d 128ul test4_p 128ul test4_q
    test4_r2 8ul test4_rBlind 128ul test4_msg 20ul test4_salt test4_sgnt_expected in
  let test = test1 && test2 && test3 && test4 in
  if test then C.String.print (C.String.of_literal "SUCCESS\n")
  else C.String.print (C.String.of_literal "Test failed\n");
  C.EXIT_SUCCESS

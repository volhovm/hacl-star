module Hacl.Impl.P256

open FStar.HyperStack.All
open FStar.HyperStack
open FStar.HyperStack.ST

module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.Curve25519.Field64.Core
module C =  Hacl.Spec.Curve25519.Field64.Core
module D = Hacl.Spec.Curve25519.Field64.Definition
open  Hacl.Spec.P256.Core
open Hacl.Spec.P256.Lemmas
open Hacl.Spec.P256.Definitions
open Hacl.Spec.P256.SolinasReduction


open Lib.Loops
open FStar.Math.Lemmas

module B = LowStar.Buffer

let felem = lbuffer uint64 (size 4)
open FStar.Mul

val addcarry:
  cin:uint64{uint_v cin <=1}
  ->  x:uint64
  -> y:uint64
  -> Pure (uint64 & uint64)
    (requires True)
    (ensures fun (r, c) -> uint_v  c < 2 /\
      uint_v  r + uint_v  c * pow2 64 == uint_v  x + uint_v  y + uint_v  cin)
      
[@CInline]
let addcarry cin  x y  =
    C.addcarry x y cin

val subborrow:
 cin:uint64{uint_v cin <= 1}
  ->  x:uint64
  -> y:uint64
  -> Pure (uint64 & uint64)
    (requires True)
    (ensures fun (r, c) -> uint_v c < 2 /\
      uint_v r - uint_v c * pow2 64 == uint_v x - uint_v y - uint_v cin)

[@CInline]
let subborrow cin x y =
  C.subborrow x y cin


#set-options "--z3rlimit 100"

val p256_add: out: felem -> arg1: felem -> arg2: felem -> 
Stack unit (requires (fun h0 ->  
  as_nat h0 arg1 < prime /\
  as_nat h0 arg2  < prime /\
live h0 out /\ live h0 arg1 /\ live h0 arg2))
(ensures (fun h0 _ h1 -> as_nat h1 out == (as_nat h0 arg1 + as_nat h0 arg2) % prime /\ as_nat h1 out < prime))
  
#set-options "--z3rlimit 400"

let p256_add out arg1 arg2  = 
  let arg2_0 = index arg2 (size 0) in 
  let arg2_1 = index arg2 (size 1) in 
  let arg2_2 = index arg2 (size 2) in 
  let arg2_3 = index arg2 (size 3) in 

  let arg1_0 = index arg1 (size 0) in 
  let arg1_1 = index arg1 (size 1) in 
  let arg1_2 = index arg1 (size 2) in 
  let arg1_3 = index arg1 (size 3) in 

 (* let a = (arg2_0, arg2_1, arg2_2, arg2_3) in 
  let b = (arg1_0, arg1_1, arg1_2, arg1_3) in 
  *)
  let (r0, r1, r2, r3) = felem_add (arg2_0, arg2_1, arg2_2, arg2_3) (arg1_0, arg1_1, arg1_2, arg1_3) in   
  
  upd out (size 0) r0;
  upd out (size 1) r1;
  upd out (size 2) r2;
  upd out (size 3) r3;
  ()

val p256_sub: out: felem -> arg1: felem -> arg2: felem -> 
Stack unit 
(requires (fun h0 -> live h0 out /\ live h0 arg1 /\ live h0 arg2 /\ as_nat h0 arg1 < prime /\
as_nat h0 arg2 < prime))
(ensures (fun h0 _ h1 -> as_nat h1 out == (as_nat h0 arg1 - as_nat h0 arg2) % prime /\ as_nat h1 out < prime ))


let p256_sub out arg1 arg2 = 
  let arg1_0 = index arg1 (size 0) in 
  let arg1_1 = index arg1 (size 1) in 
  let arg1_2 = index arg1 (size 2) in 
  let arg1_3 = index arg1 (size 3) in 
  
  let arg2_0 = index arg2 (size 0) in 
  let arg2_1 = index arg2 (size 1) in 
  let arg2_2 = index arg2 (size 2) in 
  let arg2_3 = index arg2 (size 3) in 

  let a = (arg1_0, arg1_1, arg1_2, arg1_3) in 
  let b = (arg2_0, arg2_1, arg2_2, arg2_3) in 

  let (r0, r1, r2, r3) = felem_sub a b in 
  
  upd out (size 0) r0;
  upd out (size 1) r1;
  upd out (size 2) r2;
  upd out (size 3) r3;

  ()


let longelem = lbuffer uint64 (size 8)

#set-options "--z3rlimit 100"

val sub4:
    f1:felem4
  -> f2:felem4
  -> Tot (uint64 & felem4)

let sub4 f1 f2 =
    C.sub4 f1 f2

val prime_as_felem : unit -> Tot felem4

let prime_as_felem () = 
  let a0 = u64 0xffffffffffffffff in
  let a1 = u64 0x00000000ffffffff in 
  let a2 = u64 0 in 
  let a3 = u64 0xffffffff00000001 in 
  (a0, a1, a2, a3)
     

val shift_left_update:  before: felem ->result: felem ->  Stack unit 
  (requires fun h ->as_nat h before < prime /\  live h before /\ live h result)
  (ensures (fun h0 _ h1 -> live h1 before /\ as_nat h1 result = (as_nat h0 before * 2) % prime))

let shift_left_update before result= 
  let a0 = index before (size 0) in 
  let a1 = index before (size 1) in
  let a2 = index before (size 2) in 
  let a3 = index before (size 3) in 

  let (o0, o1, o2, o3) = shift_left_felem (a0, a1, a2, a3) in 

  upd result (size 0) o0;
  upd result (size 1) o1;
  upd result (size 2) o2;
  upd result (size 3) o3

val solinas_fast_reduction: c: longelem ->result : felem ->   Stack unit   
  (requires (fun h -> live h c /\ disjoint result c /\ live h result)) 
  (ensures (fun h0 _ h1 -> modifies (loc result) h0 h1 /\ as_nat h1 result == wide_as_nat h0 c % prime ))

let solinas_fast_reduction c result = 
  let c0 = index c (size 0) in 
  let c1 = index c (size 1) in 
  let c2 = index c (size 2) in 
  let c3 = index c (size 3) in 
  let c4 = index c (size 4) in 
  let c5 = index c (size 5) in 
  let c6 = index c (size 6) in 
  let c7 = index c (size 7) in 

  let (r0, r1, r2, r3) = solinas_reduction (c0, c1, c2, c3, c4, c5, c6, c7) in 

  upd result (size 0) r0;
  upd result (size 1) r1;
  upd result (size 2) r2;
  upd result (size 3) r3

val solinas_fast_reduction_partially_opened: c: felem8 ->result : felem ->   Stack unit   
  (requires (fun h ->  live h result)) 
  (ensures (fun h0 _ h1 -> modifies (loc result) h0 h1 /\ as_nat h1 result == D.wide_as_nat4 c % prime ))


let solinas_fast_reduction_partially_opened c result = 
  let (r0, r1, r2, r3) = solinas_reduction c in 
  upd result (size 0) r0;
  upd result (size 1) r1;
  upd result (size 2) r2;
  upd result (size 3) r3

val toDomain: value: felem -> result: felem ->  Stack unit 
  (requires fun h ->  as_nat h value < prime /\ live h value /\live h result /\ disjoint result value)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ as_nat h1 result == (as_nat h0 value * pow2 256) % prime)

let toDomain value result = 
  let value0 = index value (size 0) in 
  let value1 = index value (size 1) in 
  let value2 = index value (size 2) in 
  let value3 = index value (size 3) in 
  let multipliedByPow256 = shift_256 (value0, value1, value2, value3) in 
  solinas_fast_reduction_partially_opened multipliedByPow256 result 

type point = lbuffer uint64 (size 12)

noextract 
let point_x_as_nat (h: mem) (e: point) : GTot nat = 
  let open Lib.Sequence in 
  let s = as_seq h e in 
  let s0 = s.[0] in
  let s1 = s.[1] in 
  let s2 = s.[2] in 
  let s3 = s.[3] in 
  D.as_nat4 (s0, s1, s2, s3)

noextract 
let point_y_as_nat (h: mem) (e: point) : GTot nat = 
  let open Lib.Sequence in 
  let s = as_seq h e in 
  let s0 = s.[4] in
  let s1 = s.[5] in 
  let s2 = s.[6] in 
  let s3 = s.[7] in 
  D.as_nat4 (s0, s1, s2, s3)

noextract 
let point_z_as_nat (h: mem) (e: point) : GTot nat = 
  let open Lib.Sequence in 
  let s = as_seq h e in 
  let s0 = s.[8] in
  let s1 = s.[9] in 
  let s2 = s.[10] in 
  let s3 = s.[11] in 
  D.as_nat4 (s0, s1, s2, s3)

val pointToDomain: p: point -> result: point -> Stack unit 
  (requires fun h -> live h p /\ live h result /\ disjoint p result /\
    point_x_as_nat h p < prime /\ point_y_as_nat h p < prime /\ point_z_as_nat h p < prime)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ 
    point_x_as_nat h1 result == (point_x_as_nat h0 p * pow2 256) % prime /\
    point_y_as_nat h1 result == (point_y_as_nat h0 p * pow2 256) % prime /\
    point_z_as_nat h1 result == (point_z_as_nat h0 p * pow2 256) % prime )

let pointToDomain p result = 
    let p_x = sub p (size 0) (size 4) in 
    let p_y = sub p (size 4) (size 4) in 
    let p_z = sub p (size 8) (size 4) in 
    
    let r_x = sub result (size 0) (size 4) in 
    let r_y = sub result (size 4) (size 4) in 
    let r_z = sub result (size 8) (size 4) in 

    toDomain p_x r_x;
    toDomain p_y r_y;
    toDomain p_z r_z

val mul: out: longelem -> f1: felem -> r:felem -> Stack unit
    (requires fun h -> live h out /\ live h f1 /\ live h r)
    (ensures  fun h0 _ h1 ->modifies (loc out) h0 h1 /\ wide_as_nat h1 out == as_nat h0 f1 * as_nat h0 r)
      
[@ CInline]
let mul out f1 r =
  let f10 = f1.(0ul) in
  let f11 = f1.(1ul) in
  let f12 = f1.(2ul) in
  let f13 = f1.(3ul) in

  let r0 = r.(0ul) in
  let r1 = r.(1ul) in
  let r2 = r.(2ul) in
  let r3 = r.(3ul) in
  let out8 = C.mul4 (f10, f11, f12, f13) (r0, r1, r2, r3) in
  let (o0, o1, o2, o3, o4, o5, o6, o7) = out8 in
  out.(0ul) <- o0;
  out.(1ul) <- o1;
  out.(2ul) <- o2;
  out.(3ul) <- o3;
  out.(4ul) <- o4;
  out.(5ul) <- o5;
  out.(6ul) <- o6;
  out.(7ul) <- o7
  

val load_prime: out: felem -> Stack unit 
  (requires (fun h -> live h out)) 
  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1 /\ as_nat h1 out == prime))


let load_prime out = 
  let (r0, r1, r2, r3) = upload_prime() in 
  upd out (size 0) r0;
  upd out (size 1) r1;
  upd out (size 2) r2;
  upd out (size 3) r3

val long_add: out: lbuffer uint64 (size 9) -> a: longelem -> b: longelem -> Stack unit 
  (requires fun h -> live h out /\ live h a /\ live h b)
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\ long_as_nat h1 out = wide_as_nat h0 a + wide_as_nat h0 b)


let long_add out a b = 
    let a0 = index a (size 0) in 
    let a1 = index a (size 1) in 
    let a2 = index a (size 2) in 
    let a3 = index a (size 3) in 
    let a4 = index a (size 4) in 
    let a5 = index a (size 5) in 
    let a6 = index a (size 6) in 
    let a7 = index a (size 7) in 

    let b0 = index b (size 0) in 
    let b1 = index b (size 1) in 
    let b2 = index b (size 2) in 
    let b3 = index b (size 3) in 
    let b4 = index b (size 4) in 
    let b5 = index b (size 5) in 
    let b6 = index b (size 6) in 
    let b7 = index b (size 7) in  

    let out9 = add9 (a0, a1, a2, a3, a4, a5, a6, a7) (b0, b1, b2, b3, b4, b5, b6, b7) in 
    let (o0, o1, o2, o3, o4, o5, o6, o7, o8) = out9 in 
    upd out (size 0) o0;
    upd out (size 1) o1;
    upd out (size 2) o2;
    upd out (size 3) o3;
    upd out (size 4) o4;
    upd out (size 5) o5;
    upd out (size 6) o6;
    upd out (size 7) o7;
    upd out (size 8) o8
    
    

val add: out: longelem -> a: longelem -> b: longelem -> Stack unit 
  (requires fun h -> live h out /\ live h a /\ live h b /\ wide_as_nat h a < pow2 320 /\ wide_as_nat h b < pow2 448)
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\ wide_as_nat h1 out = wide_as_nat h0 a  + wide_as_nat h0 b)
  

let add out a b = 
    let a0 = index a (size 0) in 
    let a1 = index a (size 1) in 
    let a2 = index a (size 2) in 
    let a3 = index a (size 3) in 
    let a4 = index a (size 4) in 
    let a5 = index a (size 5) in 
    let a6 = index a (size 6) in 
    let a7 = index a (size 7) in 

    let b0 = index b (size 0) in 
    let b1 = index b (size 1) in 
    let b2 = index b (size 2) in 
    let b3 = index b (size 3) in 
    let b4 = index b (size 4) in 
    let b5 = index b (size 5) in 
    let b6 = index b (size 6) in 
    let b7 = index b (size 7) in  
    
    let out8 = add8_without_carry (a0, a1, a2, a3, a4, a5, a6, a7) (b0, b1, b2, b3, b4, b5, b6, b7) in 
    let (o0, o1, o2, o3, o4, o5, o6, o7) = out8 in 
    upd out (size 0) o0;
    upd out (size 1) o1;
    upd out (size 2) o2;
    upd out (size 3) o3;
    upd out (size 4) o4;
    upd out (size 5) o5;
    upd out (size 6) o6;
    upd out (size 7) o7
    
 
 val mod_64: src: longelem ->  Stack uint64
  (requires fun h ->  live h src)
  (ensures fun h0 r h1 ->modifies0 h0 h1 /\  uint_v r = wide_as_nat h0 src % pow2 64)

let mod_64 src = 
    index src (size 0) 


val short_mul: dst: longelem -> a: felem4 -> b: uint64 -> Stack unit
  (requires (fun h -> live h dst))
  (ensures (fun h0 _ h1 ->  modifies (loc dst) h0 h1 /\ wide_as_nat h1 dst = as_nat4 a * uint_v b))

let short_mul dst a b = 
    let (f0, f1, f2, f3, f4, f5, f6, f7) = shortened_mul a  b in 
    upd dst (size 0) f0;
    upd dst (size 1) f1;
    upd dst (size 2) f2;
    upd dst (size 3) f3;
    upd dst (size 4) f4;
    upd dst (size 5) f5;
    upd dst (size 6) f6;
    upd dst (size 7) f7
    

val shift_buffer_9: dst : longelem -> src: lbuffer uint64 (size 9) -> Stack unit 
  (requires fun h -> live h dst /\ live h src /\ disjoint dst src)
  (ensures fun h0 _ h1 -> modifies (loc dst) h0 h1 /\ wide_as_nat h1 dst = long_as_nat h0 src /  pow2 64)

let shift_buffer_9 dst src = 
  let s8 = index src (size 8) in 
  let s7 = index src (size 7) in 
  let s6 = index src (size 6) in 
  let s5 = index src (size 5) in 
  let s4 = index src (size 4) in 
  let s3 = index src (size 3) in 
  let s2 = index src (size 2) in 
  let s1 = index src (size 1) in 

  upd dst (size 0) s1;
  upd dst (size 1) s2;
  upd dst (size 2) s3;
  upd dst (size 3) s4; 
  upd dst (size 4) s5;
  upd dst (size 5) s6;
  upd dst (size 6) s7;
  upd dst (size 7) s8


val shift_buffer_8: dst : longelem -> src: longelem -> Stack unit 
  (requires fun h -> live h dst /\ live h src /\ disjoint dst src)
  (ensures fun h0 _ h1 -> modifies (loc dst) h0 h1 /\ wide_as_nat h1 dst = wide_as_nat h0 src / pow2 64 )


let shift_buffer_8 dst src = 
  let s7 = index src (size 7) in 
  let s6 = index src (size 6) in 
  let s5 = index src (size 5) in 
  let s4 = index src (size 4) in 
  let s3 = index src (size 3) in 
  let s2 = index src (size 2) in 
  let s1 = index src (size 1) in 

  upd dst (size 0) s1;
  upd dst (size 1) s2;
  upd dst (size 2) s3;
  upd dst (size 3) s4; 
  upd dst (size 4) s5;
  upd dst (size 5) s6;
  upd dst (size 6) s7;
  upd dst (size 7) (u64 0)

val multiplication: a: felem -> b: felem -> result: felem -> tempBuffer: lbuffer uint64 (size 33)
  ->Stack unit
  (requires fun h -> live h a /\ live h b /\ live h result /\ live h tempBuffer /\ disjoint tempBuffer result)
  (ensures fun h0 _ h1 -> live h1 a /\ live h1 b /\ live h1 result)

let multiplication a b result tempBuffer = 
  let h0 = ST.get() in 
  let inv (h1: HyperStack.mem) (i: nat) : Type0 = 
    live h1 tempBuffer in   
  for (size 0) (size 33) inv (fun (x: size_t {size_v x < 33}) -> upd tempBuffer x (u64 0));
    
    let t = sub tempBuffer (size 0) (size 8) in 
    let t2 = sub tempBuffer (size 8) (size 8) in 
    let t3_first_round = sub tempBuffer (size 16) (size 9) in 
    let t3 = sub tempBuffer (size 25) (size 8) in  

    let prime = upload_prime() in 

    mul t a b;
(*  t< 2**512*)
    let t1 = mod_64 t in 
(* t1 < 2**64 *)    
    short_mul t2 prime t1;
(* t2 < 2**320 *)
    long_add t3_first_round t t2;
(* *)    
    shift_buffer_9 t t3_first_round;

       let t1 = mod_64 t in
    short_mul t2 prime t1;
    add t3 t t2;
    shift_buffer_8 t t3;
    
        let t1 = mod_64 t in
    short_mul t2 prime t1;
    add t3 t t2;
    shift_buffer_8 t t3;
    
        let t1 = mod_64 t in
    short_mul t2 prime t1;
    add t3 t t2;
    shift_buffer_8 t t3;
   
    let x8 = index t (size 4) in 
    let t0 = index t (size 0) in 
    let t1 = index t (size 1) in 
    let t2 = index t (size 2) in 
    let t3 = index t (size 3) in 

    let (x19, x20, x21, x22) =  reduction_prime_2prime_with_carry x8 (t0, t1, t2, t3) in 
    upd result (size 0) x19;
    upd result (size 1) x20;
    upd result (size 2) x21;
    upd result (size 3) x22


val fromDomain: f: felem-> result: felem-> tempBuffer: lbuffer uint64 (size 41) -> Stack unit
  (requires fun h -> live h f /\ live h result /\ live h tempBuffer/\ disjoint tempBuffer result)
  (ensures fun h0 _ h1 -> live h1 f /\ live h1 result /\ live h1 tempBuffer)


let fromDomain f result tempBuffer = 
  let one = sub tempBuffer (size 0) (size 4) in 
  let tempBufferForMult = sub tempBuffer (size 4) (size 37) in 
    upd one (size 0) (u64 1);
    upd one (size 1) (u64 0);
    upd one (size 2) (u64 0);
    upd one (size 3) (u64 0);
  multiplication f one result tempBufferForMult  
    
  
val pointFromDomain: p: point -> result: point ->tempBuffer: lbuffer uint64 (size 41) -> Stack unit 
  (requires fun h -> live h p /\ live h result /\ live h tempBuffer /\ disjoint result tempBuffer)
  (ensures fun h0 _ h1 -> live h1 p /\ live h1 result /\ live h1 tempBuffer)

let pointFromDomain p result tempBuffer = 
    let p_x = sub p (size 0) (size 4) in 
    let p_y = sub p (size 4) (size 4) in 
    let p_z = sub p (size 8) (size 4) in 

    let r_x = sub result (size 0) (size 4) in 
    let r_y = sub result (size 4) (size 4) in 
    let r_z = sub result (size 8) (size 4) in 

    fromDomain p_x r_x tempBuffer;
    fromDomain p_y r_y tempBuffer;
    fromDomain p_z r_z tempBuffer


val square: a: felem -> result: felem-> tempBuffer: lbuffer uint64 (size 37)  -> Stack unit
  (requires fun h -> live h a /\ live h result /\ live h tempBuffer /\ disjoint result tempBuffer)
  (ensures fun h0 _ h1 -> live h1 a /\ live h1 result /\ live h1 tempBuffer)

let square a result tempBuffer = multiplication a a result tempBuffer

(* from result to result? *)
val cube: a: felem -> result: felem -> tempBuffer : lbuffer uint64 (size 37) -> Stack unit
  (requires fun h -> live h a /\ live h result /\ live h tempBuffer /\ disjoint result tempBuffer)
  (ensures fun h0 _ h1 -> live h1 a /\ live h1 result /\ live h1 tempBuffer)

let cube a result tempBuffer = 
    square a result tempBuffer;
    multiplication a result result tempBuffer


val quatre: a: felem -> result: felem-> tempBuffer: lbuffer uint64 (size 37)  -> Stack unit
  (requires fun h -> live h a /\ live h result /\ live h tempBuffer /\ disjoint result tempBuffer)
  (ensures fun h0 _ h1 -> live h1 a /\ live h1 result /\ live h1 tempBuffer)

let quatre a result tempBuffer = 
  square a result tempBuffer;
  square result result tempBuffer


val multByTwo: value: felem -> result: felem -> Stack unit 
  (requires fun h -> live h value /\ live h result /\ disjoint value result )
  (ensures fun h0 _ h1 -> live h1 value /\ live h1 result)

let multByTwo value result = shift_left_update value result


val multByThree: value: felem -> result: felem -> Stack unit
  (requires fun h -> live h value /\ live h result /\ disjoint value result)
  (ensures fun h0 _ h1 -> live h1 value)

let multByThree value result = 
    multByTwo value result;
    let prime = prime_as_felem() in 
    p256_add result result value;
    let r0_f = index result (size 0) in 
    let r1_f = index result (size 1) in 
    let r2_f = index result (size 2) in 
    let r3_f = index result (size 3) in 
    let (borrowed, lessPrime) = sub4 (r0_f, r1_f, r2_f, r3_f) prime in 
      if eq_u64 borrowed (u64 0) then 
      begin
	let (r0_u, r1_u, r2_u, r3_u) = lessPrime in 
	upd result (size 0) r0_u;
	upd result (size 1) r1_u;
	upd result (size 2) r2_u;
	upd result (size 3) r3_u
      end   
    else    
      begin
	upd result (size 0) r0_f;
	upd result (size 1) r1_f;
	upd result (size 2) r2_f;
	upd result (size 3) r3_f
      end
	

val multByFour: value: felem -> result: felem -> tempBuffer: felem ->  Stack unit
  (requires fun h -> live h value /\ live h result /\ live h tempBuffer /\
  disjoint value result /\ disjoint value tempBuffer /\ disjoint result tempBuffer)
  (ensures fun h0 _ h1 -> live h1 value)

let multByFour value result tempBuffer = 
  multByTwo value tempBuffer;
  multByTwo tempBuffer result


val multByEight: value: felem -> result: felem ->tempBuffer: lbuffer uint64 (size 8)->  Stack unit
  (requires fun h -> live h value /\ live h result /\ live h tempBuffer /\
    disjoint value tempBuffer/\ disjoint value result /\ disjoint tempBuffer result)
  (ensures fun h0 _ h1 -> live h1 value)

let multByEight value result tempBuffer = 
  let tempForFour = sub tempBuffer (size 0) (size 4) in 
  let tempForResult = sub tempBuffer (size 4) (size 4) in 
  multByFour value tempForResult tempForFour;
  multByTwo tempForResult result


val multByMinusThree: value: felem -> result: felem -> tempBuffer: felem -> Stack unit
  (requires fun h -> live h value /\ live h result/\ live h tempBuffer /\ 
  disjoint value result /\ as_nat h value < prime)
  (ensures fun h0 _ h1 -> True)

let multByMinusThree value result tempBuffer = 
  load_prime tempBuffer;
  multByThree value result;
  p256_sub result tempBuffer result

val isOne: f: felem -> Stack bool
  (requires fun h -> live h f)
  (ensures fun h0 _ h1 -> live h1 f)

let isOne f = 
  let a0 = index f (size 0) in 
  let a1 = index f (size 1) in 
  let a2 = index f (size 2) in 
  let a3 = index f (size 3) in 
  let zero = u64 0 in 
  let one = u64 1 in 
  eq_u64 a0 one && eq_u64 a1 zero && eq_u64 a2 zero && eq_u64 a3 zero


val isZero:  f: felem -> Stack bool
  (requires fun h -> live h f)
  (ensures fun h0 _ h1 -> live h1 f)

let isZero f = 
  let a0 = index f (size 0) in 
  let a1 = index f (size 1) in 
  let a2 = index f (size 2) in 
  let a3 = index f (size 3) in 
  let zero = u64 0 in 
  eq_u64 a0 zero && eq_u64 a1 zero && eq_u64 a2 zero && eq_u64 a3 zero


val isPointAtInfinity: p: point -> Stack bool 
  (requires fun h -> live h p)
  (ensures fun h0 _ h1 -> live h1 p)


let isPointAtInfinity p = 
    let p_x = sub p (size 0) (size 4) in 
    let p_y = sub p (size 4) (size 4) in 
    let p_z = sub p (size 8) (size 4) in 
    let x_result = isOne p_x in  
    let y_result = isOne p_y in 
    let z_result = isZero p_z in 
    x_result && y_result && z_result


val loadPointAtInfinity: p: point -> Stack unit 
  (requires fun h -> live h p)
  (ensures fun h0 _ h1 -> True)

let loadPointAtInfinity p = 
   upd p (size 0) (u64 1);
   upd p (size 1) (u64 0);
   upd p (size 2) (u64 0);
   upd p (size 3) (u64 0);
   
   upd p (size 4) (u64 1);   
   upd p (size 5) (u64 0);
   upd p (size 6) (u64 0);
   upd p (size 7) (u64 0);
   
   upd p (size 8) (u64 0);   
   upd p (size 9) (u64 0);
   upd p (size 10) (u64 0);
   upd p (size 11) (u64 0)   



val copy_point: p: point -> result: point -> Stack unit 
  (requires fun h -> live h p /\ live h result /\ disjoint p result) (ensures fun h0 _ h1 -> True)

let copy_point p result = 
  copy p result

val point_double: p: point -> result: point ->  tempBuffer: lbuffer uint64 (size 117) -> Stack unit
  (requires fun h -> live h p /\ live h result /\ live h tempBuffer /\ disjoint p result /\ disjoint tempBuffer result)
  (ensures fun h0 _ h1 -> live h1 result)


let point_double p result tempBuffer = 

  let tempBuffer4 = sub tempBuffer (size 0) (size 4) in 
  let tempBuffer37 = sub tempBuffer (size 4) (size 37) in
  let s = sub tempBuffer (size 41) (size 4) in 

  let tempBuffer8 = sub tempBuffer (size 53) (size 8) in 
  let tempBuffer4_1 = sub tempBuffer (size 45) (size 4) in 
  let tempBuffer4_2 = sub tempBuffer (size 49) (size 4) in 
  let m = sub tempBuffer (size 61) (size 4) in 
  let ySquareBuffer = sub tempBuffer (size 65) (size 4) in 
  let xyy = sub tempBuffer (size 69) (size 4) in 
  let zzzz = sub tempBuffer (size 73) (size 4) in 

  let x3 = sub result (size 0) (size 4) in 
  let y3 = sub result (size 4) (size 4) in 
  let z3 = sub result (size 8) (size 4) in 

  let p_infinity = isPointAtInfinity p in 
  if p_infinity then 
    copy_point p result
  else
    let p_x = sub p (size 0) (size 4) in 
    let p_y = sub p (size 4) (size 4) in 
    let p_z = sub p (size 8) (size 4) in 

    square p_y ySquareBuffer tempBuffer37;
    (* tempBuffer4 = p_y * p_y *)
    multiplication p_x ySquareBuffer xyy tempBuffer37; 
      (* 
	tempBuffer4 = x * tempBuffer4 
	tempBuffer4 = x * y * y
      *)
    multByFour xyy s tempBuffer4_1;
      (* 
	s = tempBuffer4 * 4 
	s = x * y * y * 4
      *)
      
    quatre p_z zzzz tempBuffer37;
      (* 
	tempBuffer4 = z * z *  z * z
      *)
    let h0 =   ST.get() in 
    assume (as_nat h0 tempBuffer4 < prime);
    multByMinusThree zzzz tempBuffer4_1 tempBuffer4_2; 
      (*
	tempBuffer4_1 = tempBuffer4 * -3
	tempBuffer4_1 = z * z * z * z * -3
      *)
    square p_x tempBuffer4 tempBuffer37;
      (*
	tempBuffer4 = x * x
      *)
    multByThree tempBuffer4 tempBuffer4_2;
      (*
	tempBuffer4_2 = tempBuffer4 * 3
	tempBuffer4_2 = x * x * 3
      *)

    let h1 =   ST.get() in 
    assume (as_nat h1 tempBuffer4_1 < prime);
    assume (as_nat h1 tempBuffer4_2 < prime);
    p256_add m tempBuffer4_2 tempBuffer4_1;
      (*
	m = tempBuffer4 + tempBuffer4_1
	m = z * z * z * z * -3 + x * x * 3
      *)

    multByTwo s tempBuffer4;
      (* tempBuffer4 = s * 2  *)
    square m tempBuffer4_1 tempBuffer37;
      (* tempBuffer4_1 = m * m *)
    p256_sub x3 tempBuffer4_1 tempBuffer4;
      (*
	 x3 = tempBuffer4 - tempBuffer4_1
	 x3 = m * m  - 2 * s 
      *)

    quatre p_y tempBuffer4 tempBuffer37;
      (* tempBuffer4 = y * y * y * y *)
    multByEight tempBuffer4 tempBuffer4_2  tempBuffer8;
      (* tempBuffer4_2 = tempBuffer4 * 8
	 tempBuffer4_2 = y * y * y * y * 8
      *)
    p256_sub tempBuffer4_1 s x3;
      (*tempBuffer4_1 = s - x3 *)
    multiplication m tempBuffer4_1 tempBuffer4_1 tempBuffer37; 
      (* 
	tempBuffer4_1 = m * tempBuffer4_1 
	tempBuffer4_1 = m * (s - x3)
	 
      *)
    p256_sub y3 tempBuffer4_1 tempBuffer4_2;
      (*
	y3 = tempBuffer4_1 - tempBuffer4_2
	y3 = m * (s - x3) - 8 * y^4
      *) 

    multiplication p_y p_z tempBuffer4 tempBuffer37; 
      (*
        tempBuffer4 = py *  px 
      *)
    
    multByTwo tempBuffer4 z3  
    (* 
      z3 = tempBuffer4 * 2
      z3 = py * px * 2
    *)

val generateMask: position: size_t{size_v position < 256} -> maskResult: felem -> Stack unit
  (requires fun h -> live h maskResult)
  (ensures fun h0 _ h1 -> True)

let generateMask position maskResult = 
  let positionWord = shift_right position (size 6) in 
  let positionValue:size_t = position -! (positionWord <<. (size 6)) in 
  let value = (u64 1) <<. positionValue  in 
  upd maskResult (size 0) (u64 0);
  upd maskResult (size 1) (u64 0);
  upd maskResult (size 2) (u64 0);
  upd maskResult (size 3) (u64 0);
  upd maskResult positionWord value

val getIBit: f: felem -> position: size_t{size_v position < 256} ->tempBuffer: lbuffer uint64 (size 4) ->
Stack bool 
  (requires fun h -> live h f /\ live h tempBuffer)
  (ensures fun h0 _ h1 -> True)

let getIBit f position tempBuffer = 
  generateMask position tempBuffer;
  let f0 = index f (size 0) in 
  let f1 = index f (size 1) in 
  let f2 = index f (size 2) in 
  let f3 = index f (size 3) in 

  let mask0 = index tempBuffer (size 0) in 
  let mask1 = index tempBuffer (size 1) in 
  let mask2 = index tempBuffer (size 2) in 
  let mask3 = index tempBuffer (size 3) in 

  let r0 = logand f0 mask0 in 
  let r1 = logand f1 mask1 in 
  let r2 = logand f2 mask2 in 
  let r3 = logand f3 mask3 in 

  not(eq_0_u64 r0 && eq_0_u64 r1 && eq_0_u64 r2 && eq_0_u64 r3)


val bitOperation: x1: felem -> x2: felem ->  power: felem ->
  position: size_t{size_v position < 256} ->tempBuffer: lbuffer uint64 (size 41) -> 
  Stack unit
    (requires fun h -> 
    live h x1 /\ live h x2 /\ live h power /\ live h tempBuffer /\ 
    disjoint tempBuffer x1 /\ disjoint tempBuffer x2)
    (ensures fun h0 _ h1 -> True)

let bitOperation x1 x2 power position tempBuffer  =
  let mask = sub tempBuffer (size 0) (size 4) in 
  let tempBuffer37 = sub tempBuffer (size 4) (size 37) in 
  let bit = getIBit power ((size 255) -. position) mask in 
  if bit then
    begin
      multiplication x1 x2 x1 tempBuffer37;
      multiplication x2 x2 x2 tempBuffer37
    end
  else
    begin 
      multiplication x1 x2 x2 tempBuffer37;
      multiplication x1 x1 x1 tempBuffer37
    end  
  
val _exponent: value: felem -> power: felem -> result: felem ->
  tempBuffer: lbuffer uint64 (size 49) ->
  Stack unit 
  (requires fun h -> live h value /\ live h power /\ live h result /\ live h tempBuffer /\ disjoint value tempBuffer /\ disjoint result tempBuffer)
  (ensures fun h0 _ h1 -> True)

let _exponent value power result  tempBuffer = 
  let x1 = sub tempBuffer (size 0) (size 4) in 
  let x2 = sub tempBuffer (size 4) (size 4) in 
  let bufferComputationsInside = sub tempBuffer (size 8) (size 41) in 
  let tempBuffer37 = sub tempBuffer (size 12) (size 37) in 
  upd x1 (size 0) (u64 1);
  upd x1 (size 1) (u64 18446744069414584320);
  upd x1 (size 2) (u64 18446744073709551615);
  upd x1 (size 3) (u64 4294967294);
  copy x2 value;
  let h0 = ST.get () in 
  let inv (h1: HyperStack.mem) (i: nat) : Type0 =
  live h1 x1 /\ live h1 x2 /\ live h1 power /\ live h1 bufferComputationsInside /\ disjoint bufferComputationsInside x1 /\ disjoint bufferComputationsInside x2 in  
  for (size 0) (size 256) inv (fun (x: size_t{size_v x < 256}) -> bitOperation x1 x2 power x bufferComputationsInside);
  copy result x1


val exponent: value: felem -> power: felem -> result: felem -> tempBuffer: lbuffer uint64 (size 57) -> Stack unit (requires fun h -> live h value /\ live h power /\ live h result /\ live h tempBuffer
/\ disjoint value tempBuffer /\ disjoint result tempBuffer)
(ensures fun h0 _ h1 -> True)

let exponent value power result tempBuffer = 
    let resultForDomain = sub tempBuffer (size 0) (size 4) in 
    let tempBufferForDomain = sub tempBuffer (size 4) (size 52) in 
    let tempBufferForExponent = sub tempBuffer (size 4) (size 49) in 
    let tempBufferForFromDomain = sub tempBuffer (size 4) (size 41) in 
    toDomain value resultForDomain;
    _exponent resultForDomain power result tempBufferForExponent;
    fromDomain result result tempBufferForFromDomain

  
val norm: p: point -> resultPoint: point -> tempBuffer: lbuffer uint64 (size 68) -> Stack unit
  (requires fun h -> live h p /\ live h resultPoint /\ live h tempBuffer /\ disjoint p tempBuffer /\ disjoint tempBuffer resultPoint)
  (ensures fun h0 _ h1 -> True)
  
let norm p resultPoint tempBuffer = 
  let xf = sub p (size 0) (size 4) in
  let yf = sub p (size 4) (size 4) in 
  let zf = sub p (size 8) (size 4) in 

  let resultX = sub resultPoint (size 0) (size 4) in 
  let resultY = sub resultPoint (size 4) (size 4) in 
  let resultZ = sub resultPoint (size 8) (size 4) in 
  
  let z2f = sub tempBuffer (size 4) (size 4) in 
  let z3f = sub tempBuffer (size 8) (size 4) in
  let order_inv = sub tempBuffer (size 12) (size 4) in 

  let tempBuffer52 = sub tempBuffer (size 16) (size 52) in 
  let tempBuffer37 = sub tempBuffer (size 16) (size 37) in 
  let tempBuffer41 = sub tempBuffer (size 16) (size 41) in 
  let tempBuffer49 = sub tempBuffer (size 16) (size 49) in 
  
  square zf z2f tempBuffer37;
  cube zf z3f tempBuffer37;

  upd order_inv (size 0) (u64 18446744073709551613);
  upd order_inv (size 1) (u64 4294967295);
  upd order_inv (size 2) (u64 0);
  upd order_inv (size 3) (u64 18446744069414584321);

  _exponent z2f order_inv z2f tempBuffer49;
  _exponent z3f order_inv z3f tempBuffer49;

  multiplication xf z2f z2f tempBuffer37;
  multiplication yf z3f z3f tempBuffer37;

  fromDomain z2f resultX tempBuffer41;
  fromDomain z3f resultY tempBuffer41;
  upd resultZ (size 0) (u64 1);
  upd resultZ (size 1) (u64 0);
  upd resultZ (size 2) (u64 0);
  upd resultZ (size 3) (u64 0)


val equal_felem: f1: felem -> f2: felem -> Stack bool 
  (requires fun h -> live h f1 /\ live h f2)
  (ensures fun h0 _ h1 -> True)

let equal_felem f1 f2 = 
  let f1_0 = index f1 (size 0) in 
  let f1_1 = index f1 (size 1) in 
  let f1_2 = index f1 (size 2) in 
  let f1_3 = index f1 (size 3) in 

  let f2_0 = index f2 (size 0) in 
  let f2_1 = index f2 (size 1) in 
  let f2_2 = index f2 (size 2) in
  let f2_3 = index f2 (size 3) in 

  let r_0 = logand f1_0 f2_0 in 
  let r_1 = logand f1_1 f2_1 in 
  let r_2 = logand f1_2 f2_2 in 
  let r_3 = logand f1_3 f2_3 in 

  eq_u64 r_0 f1_0 && 
  eq_u64 r_1 f1_1 && 
  eq_u64 r_2 f1_2 && 
  eq_u64 r_3 f1_3


val point_add: p: point -> q: point -> result: point -> tempBuffer: lbuffer uint64 (size 117) -> 
   Stack unit (requires fun h -> live h p /\ live h q /\ live h result /\ live h tempBuffer /\ disjoint p result /\ disjoint p tempBuffer /\ disjoint p q /\ disjoint q result /\ disjoint q tempBuffer /\ disjoint result tempBuffer)
   (ensures fun h0 _ h1 -> True)

let point_add p q result tempBuffer = 
   let x1 = sub p (size 0) (size 4) in 
   let y1 = sub p (size 4) (size 4) in 
   let z1 = sub p (size 8) (size 4) in 

   let x2 = sub q (size 0) (size 4) in 
   let y2 = sub q (size 4) (size 4) in 
   let z2 = sub q (size 8) (size 4) in 

   let x3 = sub result (size 0) (size 4) in 
   let y3 = sub result (size 4) (size 4) in 
   let z3 = sub result (size 8) (size 4) in 

   let tempBuffer37 = sub tempBuffer (size 0) (size 37) in 
   let z2Square = sub tempBuffer (size 37) (size 4) in 
   let z1Square = sub tempBuffer (size 41) (size 4) in 
   let z2Cube = sub tempBuffer (size 45) (size 4) in 
   let z1Cube = sub tempBuffer (size 49) (size 4) in 
   let u1 = sub tempBuffer (size 53) (size 4) in 
   let u2 = sub tempBuffer (size 57) (size 4) in 
   let s1 = sub tempBuffer (size 61) (size 4) in 
   let s2 = sub tempBuffer (size 65) (size 4) in 

   let h = sub tempBuffer (size 69) (size 4) in 
   let r = sub tempBuffer (size 73) (size 4) in 
   let hSquare = sub tempBuffer (size 77) (size 4) in 
   let uh = sub tempBuffer (size 81) (size 4) in 
   let twouh = sub tempBuffer (size 85) (size 4) in 
   let rSquare = sub tempBuffer (size 89) (size 4) in 
   let hCube = sub tempBuffer (size 93) (size 4) in 
   let r_h = sub tempBuffer (size 97) (size 4) in 
   let s1hCube = sub tempBuffer (size 101) (size 4) in 
   let u1hx3 = sub tempBuffer (size 105) (size 4) in 
   let ru1hx3 = sub tempBuffer (size 109) (size 4) in 
   let z1z2 = sub tempBuffer (size 113) (size 4) in 
   
   let p_infinity = isPointAtInfinity p in 
   if p_infinity then 
     copy_point p result
   else   
   let q_infinity = isPointAtInfinity q in 
   if q_infinity then 
     copy_point q result
   else   
   begin 
     square z2 z2Square tempBuffer37;
     square z1 z1Square tempBuffer37;
     cube z2 z2Cube tempBuffer37;
     cube z1 z1Cube tempBuffer37;

     multiplication x1 z2Square u1 tempBuffer37;
     multiplication x2 z1Square u2 tempBuffer37;
     multiplication y1 z2Cube s1 tempBuffer37;
     multiplication y2 z1Cube s2 tempBuffer37;

     if equal_felem u1 u2 then 
       if equal_felem s1 s2 then 
         point_double p result tempBuffer
       else
	 loadPointAtInfinity result
     else
     begin 
       p256_sub h u2 u1;
       p256_sub r s2 s1;
       square h hSquare tempBuffer37;
       multiplication u1 hSquare uh tempBuffer37;
       multByTwo uh twouh;
       square r rSquare tempBuffer37;
       cube h hCube tempBuffer37;
       p256_sub r_h rSquare hCube;
       p256_sub x3 r_h twouh;

       multiplication s1 hCube s1hCube tempBuffer37;
       p256_sub u1hx3 uh x3;
       multiplication r u1hx3 ru1hx3 tempBuffer37;
       p256_sub y3 ru1hx3 s1hCube;

       multiplication z1 z2 z1z2 tempBuffer37;
       multiplication h z1z2 z3 tempBuffer37
     end  
   end  
       
       
  
    
    
    
   

  


module Hacl.Spec.P256.MontgomeryMultiplication

open Lib.IntTypes
open FStar.Math.Lemmas
open FStar.Math.Lib
open Hacl.Spec.P256.Lemmas
open Hacl.Spec.P256.Definitions

open Hacl.Spec.Curve25519.Field64.Definition
open Hacl.Spec.P256.Core



open FStar.HyperStack.All
open FStar.HyperStack
open FStar.HyperStack.ST

module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack

open Lib.Buffer
open Lib.Sequence

open Hacl.Impl.Curve25519.Field64.Core
module C =  Hacl.Spec.Curve25519.Field64.Core
module D = Hacl.Spec.Curve25519.Field64.Definition
open  Hacl.Spec.P256.Core
module Loop = Lib.LoopCombinators


open Lib.Loops

open FStar.Mul


noextract
val fromDomain_: a: int -> Tot (r: nat (*{ r = a * modp_inv2 (pow2 256) % prime}*))

noextract
val toDomain_: a: int -> Tot (r: nat (*{r =  a * pow2 256 % prime}*))

val lemmaFromDomain: a: int -> Lemma (fromDomain_ (a) == a * modp_inv2 (pow2 256) % prime)

val lemmaToDomainAndBackIsTheSame: a: nat { a < prime} -> Lemma (fromDomain_ (toDomain_ a) == a)
  [SMTPat (fromDomain_ (toDomain_ a))]

val lemmaFromDomainToDomain: a: nat { a < prime} -> Lemma (toDomain_ (fromDomain_ a) == a)

noextract
val pow: a:nat -> b:nat -> res:nat


noextract 
val felem_add_seq: a: felem_seq{felem_seq_as_nat a < prime} -> b: felem_seq{felem_seq_as_nat b < prime} -> 
  Tot (r: felem_seq {felem_seq_as_nat r < prime /\ felem_seq_as_nat r = toDomain_ ((fromDomain_ (felem_seq_as_nat a) + fromDomain_ (felem_seq_as_nat b)) % prime)})

noextract
val felem_sub_seq: a: felem_seq{felem_seq_as_nat a < prime} -> b: felem_seq{felem_seq_as_nat b < prime} -> 
  Tot (r: felem_seq {felem_seq_as_nat r < prime /\ 
  felem_seq_as_nat r = toDomain_ ((fromDomain_ (felem_seq_as_nat a) - fromDomain_(felem_seq_as_nat b))% prime)})


noextract
val montgomery_multiplication_seq: a: felem_seq {felem_seq_as_nat a < prime} -> b: felem_seq {felem_seq_as_nat b < prime} -> Tot (r: felem_seq {felem_seq_as_nat r < prime /\ 
  felem_seq_as_nat r = toDomain_ (fromDomain_ (felem_seq_as_nat a) * fromDomain_(felem_seq_as_nat b) % prime)
  }) 

inline_for_extraction noextract    
val montgomery_multiplication_buffer: a: felem -> b: felem -> r: felem ->  Stack unit
  (requires (fun h -> live h a /\ as_nat h a < prime /\ live h b /\ live h r /\ as_nat h b < prime)) 
  (ensures (fun h0 _ h1 -> modifies1 r h0 h1 /\ 
    as_nat h1 r < prime /\ 
    (*as_nat h1 r == as_nat h0 a * as_nat h0 b * modp_inv2(pow2 256) % prime /\
    as_nat h1 r == toDomain_ (fromDomain_(as_nat h0 a) * fromDomain_ (as_nat h0 b)) *)
    as_seq h1 r == montgomery_multiplication_seq (as_seq h0 a) (as_seq h0 b)))



noextract
val mm_cube_seq: a: felem_seq {felem_seq_as_nat a < prime}-> 
  Tot (r: felem_seq {felem_seq_as_nat r < prime /\ 
  felem_seq_as_nat r = toDomain_ (fromDomain_ (felem_seq_as_nat a) * fromDomain_ (felem_seq_as_nat a) * fromDomain_ (felem_seq_as_nat a) % prime) })

noextract
val mm_quatre_seq: a: felem_seq {felem_seq_as_nat a < prime} -> 
  Tot (r: felem_seq {felem_seq_as_nat r < prime /\ 
  felem_seq_as_nat r = toDomain_ (fromDomain_ (felem_seq_as_nat a) * fromDomain_ (felem_seq_as_nat a) * fromDomain_ (felem_seq_as_nat a) * fromDomain_ (felem_seq_as_nat a) % prime)})



noextract 
val mm_byTwo_seq: a: felem_seq {felem_seq_as_nat a < prime} -> Tot (r: felem_seq {felem_seq_as_nat r < prime /\
  felem_seq_as_nat r = toDomain_ (2 * fromDomain_ (felem_seq_as_nat a) % prime)})

noextract 
val mm_byThree_seq: a: felem_seq {felem_seq_as_nat a < prime} -> Tot (r: felem_seq {felem_seq_as_nat r < prime /\
  felem_seq_as_nat r = toDomain_ (3 * fromDomain_ (felem_seq_as_nat a) % prime )})

noextract 
val mm_byFour_seq: a: felem_seq {felem_seq_as_nat a < prime} -> Tot (r: felem_seq {felem_seq_as_nat r < prime /\
  felem_seq_as_nat r = toDomain_ (4 * fromDomain_ (felem_seq_as_nat a) % prime)})

noextract 
val mm_byEight_seq: a: felem_seq {felem_seq_as_nat a < prime} -> Tot (r: felem_seq {felem_seq_as_nat r < prime /\
  felem_seq_as_nat r = toDomain_ (8 * fromDomain_ (felem_seq_as_nat a) % prime)})

noextract 
val mm_byMinusThree_seq: a: felem_seq {felem_seq_as_nat a < prime} -> Tot (r: felem_seq {felem_seq_as_nat r < prime /\
  felem_seq_as_nat r = toDomain_ ((-3) * fromDomain_ (felem_seq_as_nat a) % prime)})


val exponent: a: felem ->result: felem -> tempBuffer: lbuffer uint64 (size 20) ->  Stack unit
  (requires fun h -> live h a /\ live h tempBuffer /\ live h result /\ disjoint tempBuffer result /\ 
  disjoint a tempBuffer /\ as_nat h a < prime)
  (ensures fun h0 _ h1 -> modifies2 result tempBuffer h0 h1 /\ (let k = fromDomain_ (as_nat h0 a) in 
    as_nat h1 result =  toDomain_ ((pow k (prime-2)) % prime)))

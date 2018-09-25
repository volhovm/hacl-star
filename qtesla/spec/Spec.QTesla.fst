module Spec.QTesla

open FStar.Mul
open FStar.List.Tot.Base
open FStar.Seq
open FStar.Seq.Base
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.RawIntTypes
open FStar.Math.Lemmas
open Spec.QTesla.Sorting

open Spec.Keccak
open Spec.Frodo.Keccak

type nonzero_nat = x:nat{x > 0}

// qTESLA-I
(*
let params_lambda:nat = 95 // security parameter
let params_kappa:nat = 32 // output length of hash function in bytes (spec lists them in bits, so convert)
let params_n:size_nat = 512 // Dimension
let params_k:size_nat = 1       // #R-LWE samples (number of polynomials in e, t, a, etc)
let params_q:int = 4205569 // modulus
let params_h:nat = 30      // # of nonzero entries of output elements of Enc
let params_Le:int = 1586   // bound on e_i for checkE
let params_Ls:int = 1586   // bound on s for checkS
let params_B:nat = 1048575 // interval the randomness is chosing from during signing
let params_d:nat = 21      // number of rounded bits
let params_bGenA:int = 19  // number of blocks requested to SHAKE128 for GenA

let params_rateXOF = 168
let params_xof = shake128        // extendable output function used in PRF1: use shake128 or shake256 depending on parameters chosen
let params_hash_shake = shake128 // hash function used in hash H: use shake128 or shake256 depending on parameters chosen

// See the GenerateNTTConstants-Magma.txt script for computing these five
// constants used in NTT.
let computed_phi = 3768668
let computed_omega = 118029
let computed_phi_inv = 3764481
let computed_omega_inv = 590666
let computed_n_inv = 4197355
*)
// end qTESLA-I parameters

// qTESLA-III-speed
(*
let params_lambda:nat = 160 // security parameter
let params_kappa:nat = 32 // output length of hash function in bytes (spec lists them in bits, so convert)
let params_n:size_nat = 1024 // Dimension
let params_k:size_nat = 1       // #R-LWE samples (number of polynomials in e, t, a, etc)
let params_q:int = 8404993 // modulus
let params_h:nat = 48      // # of nonzero entries of output elements of Enc
let params_Le:int = 1147   // bound on e_i for checkE
let params_Ls:int = 1233   // bound on s for checkS
let params_B:nat = 2097151 // interval the randomness is chosing from during signing
let params_d:nat = 22      // number of rounded bits
let params_bGenA:int = 38  // number of blocks requested to SHAKE128 for GenA

let params_rateXOF = 168
let params_xof = shake128        // extendable output function used in PRF1: use shake128 or shake256 depending on parameters chosen
let params_hash_shake = shake128 // hash function used in hash H: use shake128 or shake256 depending on parameters chosen

// See the GenerateNTTConstants-Magma.txt script for computing these five
// constants used in NTT.
let computed_phi = 5216957
let computed_omega = 3851906
let computed_phi_inv = 4276303
let computed_omega_inv = 7267723
let computed_n_inv = 8396785
*)
// end qTESLA-III-speed parameters

// qTESLA-III-size
(*
let params_lambda:nat = 160 // security parameter
let params_kappa:nat = 32 // output length of hash function in bytes (spec lists them in bits, so convert)
let params_n:size_nat = 1024 // Dimension
let params_k:size_nat = 1       // #R-LWE samples (number of polynomials in e, t, a, etc)
let params_q:int = 4206593 // modulus
let params_h:nat = 48      // # of nonzero entries of output elements of Enc
let params_Le:int = 910    // bound on e_i for checkE
let params_Ls:int = 910    // bound on s for checkS
let params_B:nat = 1048575 // interval the randomness is chosing from during signing
let params_d:nat = 21      // number of rounded bits
let params_bGenA:int = 38  // number of blocks requested to SHAKE128 for GenA

let params_rateXOF = 168
let params_xof = shake128        // extendable output function used in PRF1: use shake128 or shake256 depending on parameters chosen
let params_hash_shake = shake128 // hash function used in hash H: use shake128 or shake256 depending on parameters chosen

// See the GenerateNTTConstants-Magma.txt script for computing these five
// constants used in NTT.
let computed_phi = 3999147
let computed_omega = 396526
let computed_phi_inv = 1974815
let computed_omega_inv = 3979855
let computed_n_inv = 4202485
*)
// end qTESLA-III-size parameters

// qTESLA-p-I
(*
let params_lambda:nat = 95 // security parameter
let params_kappa:nat = 32 // output length of hash function in bytes (spec lists them in bits, so convert)
let params_n:size_nat = 1024 // Dimension
let params_k:size_nat = 4       // #R-LWE samples (number of polynomials in e, t, a, etc)
let params_q:int = 485978113 // modulus
let params_h:nat = 25      // # of nonzero entries of output elements of Enc
let params_Le:int = 554    // bound on e_i for checkE
let params_Ls:int = 554    // bound on s for checkS
let params_B:nat = 2097151 // interval the randomness is chosing from during signing
let params_d:nat = 22      // number of rounded bits
let params_bGenA:int = 108 // number of blocks requested to SHAKE128 for GenA

let params_rateXOF = 168
let params_xof = shake128        // extendable output function used in PRF1: use shake128 or shake256 depending on parameters chosen
let params_hash_shake = shake128 // hash function used in hash H: use shake128 or shake256 depending on parameters chosen

// See the GenerateNTTConstants-Magma.txt script for computing these five
// constants used in NTT.
let computed_phi = 250428822
let computed_omega = 483976553
let computed_phi_inv = 195194787
let computed_omega_inv = 67220789
let computed_n_inv = 485503525
*)
// end qTESLA-p-I parameters

// qTESLA-p-III

let params_lambda:nat = 160 // security parameter
let params_kappa:nat = 32 // output length of hash function in bytes (spec lists them in bits, so convert)
let params_n:size_nat = 2048 // Dimension
let params_k:size_nat = 5       // #R-LWE samples (number of polynomials in e, t, a, etc)
let params_q:int = 1129725953 // modulus
let params_h:nat = 40      // # of nonzero entries of output elements of Enc
let params_Le:int = 901    // bound on e_i for checkE
let params_Ls:int = 901    // bound on s for checkS
let params_B:nat = 8388607 // interval the randomness is chosing from during signing
let params_d:nat = 24      // number of rounded bits
let params_bGenA:int = 180 // number of blocks requested to SHAKE128 for GenA

let params_rateXOF = 168
let params_xof = shake128        // extendable output function used in PRF1: use shake128 or shake256 depending on parameters chosen
let params_hash_shake = shake128 // hash function used in hash H: use shake128 or shake256 depending on parameters chosen

// See the GenerateNTTConstants-Magma.txt script for computing these five
// constants used in NTT.
let computed_phi = 752833504
let computed_omega = 905348506
let computed_phi_inv = 500168718
let computed_omega_inv = 224686349
let computed_n_inv = 1129174329

// end qTESLA-p-III parameters

// End of parameter settings.
let field_t = x:int{x > -params_q /\ x < params_q}

let computed_ceil_log_q:nat = 23 // Computed: ceil(log_2 q)
let computed_b:size_nat = 3           // Computed: ceil((log_2 q)/8)

let computed_ySampler_b:nat = 3  // Computed: ceil(((log_2 B) + 1)/8), B = 2^20-1
let computed_ySampler_modulus:nat = 21  // Computed: ceil(log_2 B) + 1

// Single polynomial in \mathcal{R}_q/<x^n+1>
let poly_t = Seq.lseq field_t params_n

// Set of k polynomials in \mathcal{R}/(x^n+1)
let polys_t = Seq.lseq poly_t params_k 

let qtesla_sk = tuple4 poly_t polys_t (lbytes params_kappa) (lbytes params_kappa)
let qtesla_pk = tuple2 (lbytes params_kappa) polys_t
let qtesla_sig = tuple2 poly_t (lbytes params_kappa)

val to_lseq: #a:Type0 -> s:Seq.seq a -> l:Seq.lseq a (Seq.length s){l == s}
let to_lseq #a s = s

let create_poly : poly_t = to_lseq (Seq.create params_n 0)
let create_polys : polys_t = to_lseq (Seq.create params_k create_poly)

(* These functions operate in Z_q/<x^n+1> where q is params_q and n is params_n *)

(* A lot of this polynomial ring math taken from the Kyber spec *)

(* a + b (mod q); a, b \in Z_q *)
val fadd: a:field_t -> b:field_t -> Tot field_t
let fadd a b = (a + b) % params_q

(* a - b (mod q); a, b \in Z_q *)
val fsub: a:field_t -> b:field_t -> Tot field_t
let fsub a b = (params_q + a - b) % params_q

(* a * b (mod q); a, b \in Z_q *)
val fmul: a:field_t -> b:field_t -> Tot field_t
let fmul a b = (a * b) % params_q

(* a ^ b (mod q); a, b \in Z_q *)
val fexp: e:field_t -> n:nat -> Tot field_t (decreases n)
let rec fexp e n =
  if n = 0 then 1
  else if n = 1 then e
  else
    if n % 2 = 0 then (e `fmul` e) `fexp` (n / 2)
    else e `fmul` ((e `fmul` e) `fexp` ((n-1)/2))

let ( ** ) = fmul
let ( ++ ) = fadd
let ( -- ) = fsub
let ( ^^ ) = fexp

val map2_step: res:poly_t -> f:(field_t -> field_t -> Tot field_t) -> x:poly_t -> y:poly_t -> i:size_nat{i <= params_n} -> Tot poly_t (decreases (params_n - i))
let rec map2_step res f x y i =
  if (i = Seq.length x)
  then res
  else let res = Seq.upd res i (f (Seq.index x i) (Seq.index y i)) in
       map2_step res f x y (i + 1)

val map2: f:(field_t -> field_t -> Tot field_t) -> x:poly_t -> y:poly_t -> Tot poly_t
let map2 f x y =
  let res = create_poly in
  map2_step res f x y 0

(* a + b (mod q); a, b \in \mathcal{R}_q/<x^n+1> *)
val poly_add: a:poly_t -> b:poly_t -> Tot poly_t
let poly_add a b = map2 fadd a b

(* a - b (mod q); a, b \in \mathcal{R}_q/<x^n+1> *)
val poly_sub: a:poly_t -> b:poly_t -> Tot poly_t
let poly_sub a b = map2 fsub a b

(* a o b (mod q) [pointwise coefficient multiplication]; a, b \in \mathcal{R}_q/<x^n+1> *)
val poly_pointwise_mul: a:poly_t -> b:poly_t -> Tot poly_t
let poly_pointwise_mul a b = map2 fmul a b

val ntt: p:poly_t -> Tot poly_t
let ntt p =
  let np = p in
  repeati params_k (fun i (np:poly_t) ->
		 Seq.upd np i (repeati params_k (fun j x -> x ++ ((computed_phi ^^ j) ** (Seq.index p j) ** (computed_omega ^^ (i * j)))) 0)) np

val inv_ntt: p:poly_t -> Tot poly_t
let inv_ntt p =
  let np = p in
  repeati params_n (fun i (np:poly_t) ->
		 Seq.upd np i (computed_n_inv ** (computed_phi_inv ^^ i) ** repeati params_n (fun j x -> x ++ ((Seq.index p j) ** (computed_omega_inv ^^ (i * j)))) 0)) np

(* a * b (mod q); a, b \in \mathcal{R}_q/<x^n+1> *)
(* qTESLA specific assumption: a is always in NTT form, and b is always in standard form. Use poly_mul for two polynomials in standard form. *)
val poly_ntt_mul: a:poly_t -> b:poly_t -> Tot poly_t
let poly_ntt_mul a b =
  inv_ntt (a `poly_pointwise_mul` (ntt b))

(* a * b (mod q); a, b \in \mathcal{R}_q/<x^n+1> *)
(* a, b in standard form *)
val poly_mul: a:poly_t -> b:poly_t -> Tot poly_t
let poly_mul a b =
  inv_ntt ((ntt a) `poly_pointwise_mul` (ntt b))
  
(* End of polynomial ring math *)

val sum: l:list int -> Tot int
let rec sum l =
  match l with
  | [] -> 0
  | hd :: tl -> hd + sum tl

val sort_coefficients: p: poly_t -> Tot poly_t
let sort_coefficients p = sort_lseq (<=) p
  
val poly_max_sum_helper: sorted:poly_t -> h:nat{h < Seq.length sorted} -> Tot int
let rec poly_max_sum_helper sorted h =
  let res = Seq.index sorted h in
    if h = 0
    then res
    else res + poly_max_sum_helper sorted (h - 1)

val poly_max_sum: p:poly_t -> h:nat{h < Seq.length p} -> Tot int
let poly_max_sum p h =
  let sorted = sort_coefficients p in
  perm_len sorted p;
  poly_max_sum_helper sorted h
  
// Sum the h largest coefficients of s, and return true if bounded by L_s
val checkS: s:poly_t -> Tot bool
let checkS s = poly_max_sum s params_h <= params_Ls

// Sum the h largest coefficients of e_i, and return true if bounded by L_e
val checkE: e:poly_t -> Tot bool
let checkE e = poly_max_sum e params_h <= params_Le

// Given an input pre-seed of \kappa bytes, return a buffer of (\kappa * ((k+3)/8)) bytes extended by the XOF
val prf1: preseed:lbytes params_kappa -> lbytes (params_kappa * (params_k+3))
let prf1 preseed = params_xof params_kappa preseed (params_kappa * (params_k+3))

val prf2: #mLen:size_nat{mLen < maxint SIZE - 2 * params_kappa} -> seedY: (lbytes params_kappa) -> r: (lbytes params_kappa) -> m: (lbytes mLen) -> Tot (lbytes params_kappa)
let prf2 #mLen seedY r m =
  let concatenation = concat (concat seedY r) m in
  params_xof (length concatenation) concatenation params_kappa

val genA_getC: cBuf: bytes -> cPos: size_nat{(cPos+1) * computed_b <= length cBuf} -> Tot size_nat
let genA_getC cBuf cPos = 
  let subbuffer = slice (to_lbytes cBuf) (cPos * computed_b) ((cPos+1) * computed_b) in
  nat_from_bytes_le subbuffer

val genA_updateA: a:polys_t -> i:nat{i < params_k * params_n} -> newVal:field_t -> Tot polys_t
let genA_updateA a i newVal =
  let polyNum = i / params_n in
  let coefNum = i - params_n * polyNum in
  let ax = Seq.index a polyNum in
  let axy = Seq.upd ax coefNum newVal in
    Seq.upd a polyNum ax

(* We have a strange termination condition with this while loop. If cSHAKE was completely broken, it could theoretically return an array of bytes such that every b-byte subarray interpreted as a natural number was greater than equal to the modulus parameter q. If it kept returning arrays like this, the function could theoretically loop infinitely. Of course this won't happen. It may be possible to prove something like "there is guaranteed to exist at least one element in the output array < q" but without even knowing what is provable about hash functions the F* experts thought this was difficult.

So at their suggestion this code takes a different approach: We define the function to always terminate but with the possibility of failure, and then assume the existence of an "oracle" function that somehow tells us that if we end up calling cSHAKE a certain number of times, we're guaranteed to succeed. This is what the "fuel" parameter in genA_while and the definition of genA_oracle below it are all about. *)

val genA_while: #seedALen:size_nat -> seedA: lbytes seedALen -> cBuf: bytes{length cBuf >= 2} -> s:uint16 -> a:polys_t -> pos: size_nat{(pos+1) * computed_b <= length cBuf} -> bPrime:size_nat{bPrime >= 1 /\ params_rateXOF * bPrime = length cBuf} -> i:nat -> fuel:nat -> Tot (option polys_t) (decreases %[(params_k * params_n - i); fuel])
let rec genA_while #seedALen seedA cBuf s a pos bPrime i fuel =
  if fuel = 0 then None else
  if i < params_k * params_n
    then let s, pos, bPrime, cBuf =
      if pos > ((params_rateXOF * bPrime) / computed_b) - 4
      then let s, pos, bPrime = (add_mod s (u16 1)), 0, 1 in
           let cBuf = cshake128_frodo seedALen seedA s (params_rateXOF * bPrime) in
	   s, pos, bPrime, cBuf
      else s, pos, bPrime, cBuf in
    let c_pos = genA_getC cBuf pos in
      let a, i, fuel =
        let c_pos_mod = c_pos % (pow2 computed_ceil_log_q) in
	if params_q > c_pos_mod
	then genA_updateA a i c_pos_mod, i + 1, fuel
	else a, i, fuel - 1 in
      let pos = pos + 1 in
      genA_while #seedALen seedA cBuf s a pos bPrime i fuel
    else Some a

assume val genA_oracle: #seedALen:size_nat -> seedA: lbytes seedALen -> cBuf: bytes -> s:uint16 -> a:polys_t -> pos: size_nat{(pos+1) * computed_b < length cBuf} -> bPrime:size_nat{bPrime >= 1 /\ params_rateXOF * bPrime = length cBuf} -> i:nat -> Tot (fuel:nat{Some? (genA_while #seedALen seedA cBuf s a pos bPrime i fuel)})
  
val genA: #seedALen: size_nat -> seedA: lbytes seedALen -> Tot polys_t
let genA #seedALen seedA =
  let bPrime = params_bGenA in
  let cBuf = cshake128_frodo seedALen seedA (u16 0) (params_rateXOF * bPrime) in
  let i = 0 in
  let pos = 0 in
  let a = create_polys in
  let fuel:nat = genA_oracle seedA cBuf (u16 0) a pos bPrime i in
  let res = genA_while seedA cBuf (u16 0) a pos bPrime i fuel in
  Some?.v res

// Nonce is called "nonce" to avoid confusion; in spec it is S.
// gaussSampler is assumed because it has floating point math we can't
// yet model in F*. random_bytes is assumed because it needs to come from
// an underlying system source.
assume val gaussSampler: rand: (lbytes params_kappa) -> nonce: nat{nonce > 0} -> Tot poly_t
assume val random_bytes: n: size_nat -> Tot (lbytes n)

// Termination is probabilistic due to the need to get the right sort
// of output from the sampler, and so we use the fuel method again.
val keygen_sample_while: seed: (lbytes params_kappa) -> nonce: nonzero_nat -> checkFn: (poly_t -> Tot bool) -> fuel: nat -> Tot (option (tuple2 poly_t nonzero_nat)) (decreases fuel)
let rec keygen_sample_while seed nonce checkFn fuel =
  if fuel = 0 then None else
  let s = gaussSampler seed nonce in
  if checkFn s then Some (s, nonce)
               else keygen_sample_while seed (nonce + 1) checkFn (fuel - 1)

assume val keygen_sample_oracle: seed: (lbytes params_kappa) -> nonce: nat{nonce > 0} -> checkFn: (poly_t -> Tot bool) -> Tot (fuel:nat{Some? (keygen_sample_while seed nonce checkFn fuel)})

let keygen_sampleS_while seedS nonce = Some?.v (keygen_sample_while seedS nonce checkS (keygen_sample_oracle seedS nonce checkS))
let keygen_sampleE_while seedE nonce = Some?.v (keygen_sample_while seedE nonce checkE (keygen_sample_oracle seedE nonce checkE))

#reset-options "--z3rlimit 50 --max_fuel 0"
val keygen_sampleE_step: seedE:(lbytes (params_kappa * params_k)) -> nonce:nonzero_nat -> e:polys_t -> i:size_nat{i <= Seq.length e} -> Tot (tuple2 polys_t nonzero_nat) (decreases (Seq.length e - i))
let rec keygen_sampleE_step seedE nonce e i =
  if i = Seq.length e then e, nonce
		      else let seedEi = Lib.Sequence.sub seedE (i * params_kappa) params_kappa in
		           let ei, nonce = keygen_sampleE_while seedEi nonce in
		           let e = Seq.upd e i ei in
			   keygen_sampleE_step seedE nonce e (i + 1)

val keygen_sampleE: seedE:(lbytes (params_kappa * params_k)) -> nonce:nonzero_nat -> Tot (tuple2 polys_t nonzero_nat)
let keygen_sampleE seedE nonce = 
  let e = create_polys in
  keygen_sampleE_step seedE nonce e 0

val poly_mod: f:poly_t -> n:nat{n >= 2 /\ n <= params_q} -> Tot poly_t
let poly_mod f n =
  repeati (Seq.length f)
  (fun i (f:poly_t) ->
    let fi = (Seq.index f i) % n in
    Seq.upd f i fi) f

val keygen_computeT_step: a:polys_t -> s:poly_t -> e:polys_t -> t:polys_t -> i:size_nat{i <= Seq.length a} -> Tot polys_t (decreases (Seq.length a - i))
let rec keygen_computeT_step a s e t i =
  if i = Seq.length a then t
    else // Remember, a is always in NTT form; other polys in standard form
         let ti = (((Seq.index a i) `poly_ntt_mul` s) `poly_add` (Seq.index e i)) `poly_mod` params_q in
	 let t = Seq.upd t i ti in
	 keygen_computeT_step a s e t (i + 1)

val keygen_computeT: a:polys_t -> s:poly_t -> e:polys_t -> Tot polys_t
let keygen_computeT a s e =
  let t = create_polys in
  keygen_computeT_step a s e t 0

//val qTesla_keygen: Tot (tuple2 qtesla_sk qtesla_pk)
let qTesla_keygen : tuple2 qtesla_sk qtesla_pk =
  let preseed = random_bytes params_kappa in
  let seedbuf = prf1 preseed in
  let seedS_begin = 0 in
  let seedS_len = params_kappa in
  let seedS = Lib.Sequence.sub seedbuf seedS_begin seedS_len in

  let seedE_begin = seedS_begin + seedS_len in
  let seedE_len = params_k * params_kappa in
  let seedE = Lib.Sequence.sub seedbuf seedE_begin seedE_len in

  let seedA_begin = seedE_begin + seedE_len in
  let seedA_len = params_kappa in
  let seedA = Lib.Sequence.sub seedbuf seedA_begin seedA_len in

  let seedY_begin = seedA_begin + seedA_len in
  let seedY_len = params_kappa in
  let seedY = Lib.Sequence.sub seedbuf seedY_begin seedY_len in

  let a = genA seedA in
  let nonce = 1 in
  let s, nonce = keygen_sampleS_while seedS nonce in
  let e, nonce = keygen_sampleE seedE nonce in
  let t = keygen_computeT a s e in
  let sk = (s, e, seedA, seedY) in
  let pk = (seedA, t) in
  sk, pk

let ySampler_XOF = cshake128_frodo

val ySampler_while: rand: lbytes params_kappa -> cBuf: bytes -> pos: size_nat -> nPrime: size_nat{computed_ySampler_b * nPrime <= max_size_t /\ computed_ySampler_b * nPrime = length cBuf} -> sPrime: uint16 -> i: size_nat{i <= params_n} -> y: poly_t -> fuel:nat -> Tot (option poly_t) (decreases %[(params_n - i); fuel])
let rec ySampler_while rand cBuf pos nPrime sPrime i y fuel =
  if fuel = 0 then None else
  let b = computed_ySampler_b in
  if i < params_n
  then let sPrime, pos, nPrime, cBuf =
    if pos >= nPrime 
    then let sPrime, pos, nPrime = (add_mod sPrime (u16 1)), 0, params_rateXOF / b in
         let cBuf = ySampler_XOF (length rand) rand sPrime params_rateXOF in
         sPrime, pos, nPrime, cBuf
    else sPrime, pos, nPrime, cBuf in
    let yi = (nat_from_bytes_le (slice (to_lbytes cBuf) (pos * b) ((pos + 1) * b))) % (pow2 computed_ySampler_modulus) - params_B in
    assert(yi < pow2 computed_ySampler_modulus);
    assert_norm(pow2 computed_ySampler_modulus < params_q);
    assert(yi < params_q);
    let y = Seq.upd y i yi in
    let i, fuel = if yi <> params_B + 1 then i+1, fuel else i, fuel-1 in
    let pos = pos + 1 in
    ySampler_while rand cBuf pos nPrime sPrime i y fuel
  else Some y

assume val ySampler_oracle: rand: lbytes params_kappa -> cBuf: bytes -> pos: size_nat -> nPrime: size_nat{computed_ySampler_b * nPrime <= max_size_t /\ computed_ySampler_b * nPrime = length cBuf} -> sPrime: uint16 -> i: size_nat{i <= params_n} -> y: poly_t -> Tot (fuel:nat{Some? (ySampler_while rand cBuf pos nPrime sPrime i y fuel)})

val ySampler: rand: lbytes params_kappa -> nonce: uint16 -> Tot poly_t
let ySampler rand nonce =
  let b = computed_ySampler_b in
  let y = create_poly in
  let pos, nPrime, sPrime = 0, params_n, (mul_mod nonce (u16 256)) in
  let cBuf = ySampler_XOF (length rand) rand sPrime (b * nPrime) in
  let i = 0 in
  let fuel = ySampler_oracle rand cBuf pos nPrime sPrime i y in
  Some?.v (ySampler_while rand cBuf pos nPrime sPrime i y fuel)

#reset-options "--z3rlimit 50 --max_fuel 0"
val hashH: #mlen: size_nat{params_k * params_n + mlen <= max_size_t} -> v: polys_t -> m: lbytes mlen -> Tot (lbytes params_kappa)
let hashH #mlen v m =
  let w = Lib.Sequence.create (params_k * params_n + mlen) (u8 0) in
  let w = repeati params_k
    (fun i w -> repeati params_n
      (fun j w -> let vij:field_t = (Seq.index (Seq.index v i) j) in
               assert_norm(vij % (pow2 params_d) >= 0);
	       assert_norm(vij % (pow2 params_d) < pow2 params_d);
	       assert_norm(pow2 params_d < params_q);
	       let val_:field_t = vij % (pow2 params_d) in
	       let val_:field_t = assert_norm(val_ - (pow2 params_d) > -params_q);
				     if val_ > (pow2 (params_d - 1))
				     then val_ - (pow2 params_d)
				     else val_ in
               let wiInt = (vij - val_) / (pow2 params_d) in
	       (* TODO: Patrick tells us the above math guarantees wiInt is < 2^8. We should prove this properly. Assume it for now. *)
	       assume (wiInt >= 0);
	       assume (wiInt < maxint U8);
	       let wi = u8 wiInt in
	       w.[i * params_n + j] <- wi
      ) w
    ) w in
  let w = repeati mlen
    (fun i w -> w.[params_k * params_n + i] <- m.[i]) w in
  let cPrime = params_hash_shake (length w) w params_kappa in
  cPrime

let signlist_elt = x:int{x = -1 \/ x == 1}
let signlist_t = Seq.lseq signlist_elt params_h

val enc_while_getR: #rLen:size_nat -> rBuf: (lbytes rLen) -> i:nat{i < rLen} -> Tot (x:nat{x < 256})
let enc_while_getR #rLen rBuf i =
  let byte = slice rBuf i (i+1) in
  nat_from_bytes_le byte

(* pos_list and sign_list aren't returned by this function in the spec, although they are used in the implementation. We compute them here for consistency but only return c. *)
val enc_while: cPrime: (lbytes params_kappa) -> rBuf: (lbytes params_rateXOF) -> pos_list: (Seq.lseq int params_h) -> sign_list: signlist_t -> cnt: size_nat -> c: poly_t -> s:uint16 -> i: size_nat -> fuel:nat -> Tot (option poly_t) (decreases %[(params_h - i); fuel])
let rec enc_while cPrime rBuf pos_list sign_list cnt c s i fuel =
  if fuel = 0 then None else
  if i < params_h then 
    let cnt, s, rBuf =
    if cnt > (params_rateXOF - 3)
    then let s, cnt = add_mod s (u16 1), 0 in // TODO: add_mod ok?
	 let rBuf = cshake128_frodo params_kappa cPrime s params_rateXOF in
	 cnt, s, rBuf
    else cnt, s, rBuf in
  let pos = ((enc_while_getR rBuf cnt) * 256 + (enc_while_getR rBuf (cnt+1))) % params_n in
  let c, i, fuel, pos_list, sign_list = 
    if Seq.index c pos = 0 
    then let cpos:signlist_elt = if (enc_while_getR rBuf cnt + 2) % 2 = 1 then -1 else 1 in
         let c:poly_t = Seq.upd c pos cpos in 
	 let pos_list = Seq.upd pos_list i pos in
	 let sign_list = Seq.upd sign_list i (Seq.index c pos) in
	 let i = i + 1 in
	 c, i, fuel, pos_list, sign_list
    else c, i, fuel - 1, pos_list, sign_list in
  let cnt = cnt + 3 in
  enc_while cPrime rBuf pos_list sign_list cnt c s i fuel
  else Some c
	       
assume val enc_oracle: cPrime: (lbytes params_kappa) -> rBuf: (lbytes params_rateXOF) -> pos_list: (Seq.lseq int params_h) -> sign_list: signlist_t -> cnt: size_nat{cnt < params_rateXOF - 2} -> c: poly_t -> s:uint16 -> i: size_nat -> Tot (fuel:nat{Some? (enc_while cPrime rBuf pos_list sign_list cnt c s i fuel)})

val enc: cPrime: (lbytes params_kappa) -> Tot poly_t
let enc cPrime =
  let s = (u16 0) in
  let cnt = 0 in
  let rBuf = cshake128_frodo params_kappa cPrime s params_rateXOF in
  let i = 0 in
  let c:poly_t = create_poly in
  let pos_list:(Seq.lseq int params_h) = Seq.create params_h 0 in
  let sign_list:signlist_t = Seq.create params_h 1 in 
  let fuel:nat = enc_oracle cPrime rBuf pos_list sign_list cnt c s i in
  let res = enc_while cPrime rBuf pos_list sign_list cnt c s i fuel in
  Some?.v res

val mod_pm: a:int -> n:nat{n >= 2} -> Tot (x:int{x >= -(n/2) /\ x <= n/2})
let mod_pm a n =
  let res:nat = a % n in
  if res <= n/2 
  then res 
  else res - n

let intL n =
  assert_norm(pow2 params_d >= 2);
  mod_pm n (pow2 params_d)
  
// mod_pm: R_q x Z -> R_q
val poly_mod_pm: f:poly_t -> n:nat{n >= 2} -> Tot poly_t
let poly_mod_pm f n =
  repeati (Seq.length f)
  (fun i (f:poly_t) ->
    let fi = (Seq.index f i) `mod_pm` n in
    Seq.upd f i fi) f

let fnL f = 
  assert_norm(pow2 params_d >= 2);
  poly_mod_pm f (pow2 params_d)

// [*]_M: Z -> Z
#reset-options "--z3rlimit 50 --max_fuel 0"
val intM: c: int -> Tot field_t // (x:int{x > -params_q /\ x < params_q})
let intM c = 
  assert_norm((pow2 params_d) >= 2);
  let res = ((c `mod_pm` params_q) - (c `mod_pm` (pow2 params_d))) / (pow2 params_d) in
  assume(res > -params_q); // TODO: Above line fails with --max-fuel 0 and goes off into the weeds without it, on the qTESLA-p-III parameter set.
  res
  

// [*]_M: R_q -> R_q
val fnM: f: poly_t -> Tot poly_t
let fnM f =
  repeati (Seq.length f)
  (fun i (f:poly_t) ->
    let fi = intM (Seq.index f i) in
    Seq.upd f i fi) f

// [*]_M applied to a set of polynomials f_1, ..., f_k
val polysM: p: polys_t -> Tot polys_t
let polysM p =
  repeati (Seq.length p)
  (fun i (p:polys_t) ->
    let pi = fnM (Seq.index p i) in
    Seq.upd p i pi) p

// Returns true if the polynomial is rejected. Used in signing.
val test_rejection: z:poly_t -> Tot bool
let test_rejection z =
  let (res:bool) = false in
  repeati params_n
  (fun i res -> res || ((abs (Seq.index z i)) > (params_B - params_Ls))) res

// Returns true if the polynomial is rejected. Used in verification.
val test_z: z:poly_t -> Tot bool
let test_z z =
  let (res:bool) = false in
  repeati params_n
  (fun i res -> res || 
             ((Seq.index z i) < -(params_B - params_Ls)) ||
	     ((Seq.index z i) > (params_B - params_Ls))) res

// For some reason, if I open FStar.Math.Lib to get max, it breaks the
// definition of cshake128_frodo above. So I've just copied it here since
// it's simple
let max x y = if x >= y then x else y

val lInfiniteNorm: p:poly_t -> Tot field_t
let lInfiniteNorm p =
  let maxVal:field_t = (abs (Seq.index p 0)) in
  repeati (params_n - 1)
  (fun i (maxVal:field_t) -> max maxVal (abs (Seq.index p (i+1)))) maxVal
 
val test_w: w:polys_t -> Tot bool
let test_w w =
  let (res:bool) = false in
  repeati params_k
  (fun i res -> res || 
    (lInfiniteNorm (fnL (Seq.index w i))) >= ((pow2 (params_d - 1)) - params_Le) ||
    (lInfiniteNorm (Seq.index w i)) >= (params_q / 2) - params_Le) res
    
val qtesla_sign_step4: #mLen: size_nat{params_k * params_n + mLen <= max_size_t} -> m: (lbytes mLen) -> sk: qtesla_sk -> r: (lbytes params_kappa) -> rand: (lbytes params_kappa) -> counter:uint16 -> fuel:nat -> Tot (option qtesla_sig) (decreases fuel)
let rec qtesla_sign_step4 #mLen m sk r rand counter fuel =
  if fuel = 0 then None else
  let s, e, seedA, seedY = sk in
  let y = ySampler rand counter in
  let a = genA seedA in
  let v:polys_t = Seq.create params_k (Seq.create params_n 0) in
  let v = repeati params_k 
    (fun i (v:polys_t) -> 
      let vi:poly_t = ((Seq.index a i) `poly_ntt_mul` y) `poly_mod_pm` params_q in
      Seq.upd v i vi) v in
  let cPrime = hashH (polysM v) m in
  let c = enc cPrime in
  let z = y `poly_add` (s `poly_mul` c) in
  if test_rejection z
  then qtesla_sign_step4 m sk r rand (add_mod counter (u16 1)) (fuel - 1)
  else let w:polys_t = create_polys in
       let w:polys_t = repeati params_k 
       (fun i (w:polys_t) -> 
	 let (wi:poly_t) = ((Seq.index v i) `poly_sub` ((Seq.index e i) `poly_mul` c)) `poly_mod_pm` params_q in
	 Seq.upd w i wi) w in
       if test_w w
       then qtesla_sign_step4 m sk r rand (add_mod counter (u16 1)) (fuel - 1)
       else Some (z, cPrime)

assume val qtesla_sign_oracle:  #mLen: size_nat{params_k * params_n + mLen <= max_size_t} -> m: (lbytes mLen) -> sk: qtesla_sk -> r: (lbytes params_kappa) -> rand: (lbytes params_kappa) -> counter:uint16 -> Tot (fuel:nat{Some? (qtesla_sign_step4 #mLen m sk r rand counter fuel)})

val qtesla_sign: #mLen: size_nat{params_k * params_n + mLen <= max_size_t} -> m: (lbytes mLen) -> sk: qtesla_sk -> Tot qtesla_sig
let qtesla_sign #mLen m sk =
  let s, e, seedA, seedY = sk in
  let counter = (u16 0) in
  let r = random_bytes params_kappa in
  let rand = prf2 seedY r m in
  let fuel = qtesla_sign_oracle m sk r rand counter in
  let res = qtesla_sign_step4 m sk r rand counter fuel in
  Some?.v res

let compare (#len:size_nat) (test_expected:lbytes len) (test_result:lbytes len) =
  for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) test_expected test_result

val qtesla_verify: #mLen: size_nat{params_k * params_n + mLen <= max_size_t} -> m: (lbytes mLen) -> sig: qtesla_sig -> pk: qtesla_pk -> Tot bool
let qtesla_verify #mLen m sig pk =
  let z, cPrime = sig in
  let seedA, t = pk in
  let c = enc cPrime in
  let a = genA seedA in
  let w = create_polys in
  let w = repeati params_k
    (fun i (w:polys_t) -> 
      let ai = Seq.index a i in
      let ti = Seq.index t i in
      let wi = ((ai `poly_ntt_mul` z) `poly_sub` (ti `poly_mul` c)) `poly_mod_pm` params_q in
      Seq.upd w i wi) w in
  if test_rejection z || not (compare cPrime (hashH (polysM w) m))
  then false
  else true

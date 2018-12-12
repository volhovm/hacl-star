module Hacl.Impl.QTesla

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

module I = FStar.Int
module I8 = FStar.Int8
module I16 = FStar.Int16
module I32 = FStar.Int32
module I64 = FStar.Int64
module UI16 = FStar.UInt16
module UI32 = FStar.UInt32
module UI64 = FStar.UInt64
open FStar.Int.Cast

//open LowStar.BufferOps
open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open C.Loops

open Hacl.Impl.QTesla.Params
open Hacl.Impl.QTesla.Constants
open Hacl.Impl.QTesla.Globals
open Hacl.Impl.QTesla.Parameterized

module B  = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack

module Seq = FStar.Seq
module LibSeq = Lib.Sequence

module FS   = Spec.SHA3
module SHA3 = Hacl.SHA3
module S    = Spec.QTesla

module R    = Hacl.QTesla.Random

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --admit_smt_queries true"

val mod7:
    k: I64.t
  -> Stack I64.t
    (requires fun _ -> True)
    (ensures fun h0 r h1 -> h0 == h1 /\ (I64.v r) = (I64.v k) % 7)

let mod7 k =
    push_frame();
    let i = create (size 1) k in
    for 0ul 2ul
    (fun h _ -> live h i)
    (fun _ -> i.(size 0) <- I64.( (i.(size 0) &^ 7L) +^ (i.(size 0) >>^ 3ul) ));

    let res = I64.( ((i.(size 0) -^ 7L) >>^ 3ul) &^ i.(size 0) ) in
    pop_frame();
    res

assume val sample_gauss_poly:
    x: poly
  -> seed: lbuffer uint8 crypto_randombytes
  -> nonce: FStar.Int64.t
  -> Stack unit
    (requires fun h -> live h x /\ live h seed /\ disjoint x seed)
    (ensures fun h0 _ h1 -> modifies1 x h0 h1) 
    
// Reference implementation returns the unsigned version of the element type. Not sure yet whether or not
// it's important to do this. In one case the return value is compared against a quantity that isn't even close
// to exceeding the maximum value of a signed int32, much less an int64, and in all other cases ends up getting
// immediately cast back into a signed type.
val abs_elem: value: elem -> Tot (x:elem{x >=^ (to_elem 0)})
let abs_elem value = 
    let mask = value >>^ ((size elem_n) -. (size 1)) in
    (mask ^^ value) -^ mask

val check_ES:
    p: poly
  -> bound: UI32.t
  -> Stack bool
    (requires fun h -> live h p)
    (ensures fun h0 _ h1 -> h0 == h1)

let check_ES p bound =
  push_frame();
  let sum = create (size 1) 0ul in
  let limit = create (size 1) params_n in
  let temp = create (size 1) 0s in
  let mask = create (size 1) 0s in
  let list = create params_n 0s in
  for (size 0) params_n
      (fun h _ -> live h p /\ live h list)
      (fun j ->
        let abspj = abs_elem p.(j) in
	// TODO: Heuristic parameter sets cast to the element type. Figure/find out why.
        list.(j) <- elem_to_int16 abspj);

  for (size 0) params_h
      (fun h _ -> live h p /\ live h sum /\ live h limit /\ live h temp /\ live h mask /\ live h list)
      (fun j ->
          let loopMax:UI32.t = UI32.((limit.(size 0)) -^ 1ul) in
          for 0ul loopMax
          (fun h _ -> live h p /\ live h sum /\ live h limit /\ live h temp /\ live h mask /\ live h list)
          (fun i ->
              mask.(size 0) <- I16.( ((list.(i +. (size 1))) -^ (list.(i))) >>^ 15ul );
              temp.(size 0) <- I16.( ((list.(i +. (size 1))) &^ (mask.(size 0))) |^
                                    ((list.(i)) &^ (lognot mask.(size 0))));
              list.(I16.(i +. (size 1))) <- I16.(( (list.(i)) &^ mask.(size 0) ) |^
                                         ( (list.(i +. (size 1))) &^ (lognot mask.(size 0)) ));
              list.(i) <- temp.(size 0)
          );

          let listIndex:UI32.t = UI32.((limit.(size 0)) -^ 1ul) in
          let listAmt:I16.t = list.(listIndex) in
          let listAmt:UI32.t = int16_to_uint32 listAmt in
          sum.(size 0) <- UI32.(sum.(size 0) +^ listAmt);
          limit.(size 0) <- UI32.((limit.(size 0)) -^ 1ul)
      );

   let sumAmt:UI32.t = sum.(size 0) in
   let res = UI32.(sumAmt >^ bound) in
   pop_frame();
   res

val reduce:
    a: I64.t
  -> Tot elem

let reduce a =
    let u:I64.t = I64.((a *^ params_qinv) &^ 0xffffffffL) in
    let u:I64.t = I64.(u *^ (elem_to_int64 params_q)) in
    let a:I64.t = I64.(a +^ u) in
    int64_to_elem I64.(a >>^ 32ul)

val barr_reduce:
    a: elem
  -> Tot elem

let barr_reduce a =
    let a64:I64.t = elem_to_int64 a in
    let u:elem = (int64_to_elem I64.((a64 *^ params_barr_mult) >>^ params_barr_div)) *^ params_q in
    a -^ u

open Lib.ByteBuffer

val poly_uniform:
    a: poly
  -> seed: lbuffer uint8 crypto_randombytes
  -> Stack unit
    (requires fun h -> live h a /\ live h seed /\ disjoint a seed)
    (ensures fun h0 _ h1 -> modifies1 a h0 h1)

let poly_uniform a seed =
    push_frame();
    let pos = create (size 1) (size 0) in
    let i = create (size 1) (u32 0) in
    let nbytes:size_t = (params_q_log +. 7ul) /. 8ul in
    let nblocks = create (size 1) params_genA in
    let mask:UI32.t = (1ul <<. params_q_log) -. 1ul in
    let buf = create (shake128_rate *. params_genA) (u8 0) in
    let dmsp = create (size 1) 0us in
    SHA3.cshake128_frodo crypto_randombytes seed (dmsp.(size 0)) (shake128_rate *. params_genA) buf;
    dmsp.(size 0) <- UI16.((dmsp.(size 0)) +^ 1us);

    while
        #(fun h -> live h pos /\ live h i /\ live h nblocks /\ live h buf /\ live h dmsp)
        #(fun _ h -> live h pos /\ live h i /\ live h nblocks /\ live h buf /\ live h dmsp)
        ( fun _ -> (i.(size 0)) <. (params_k *. params_n) )
        ( fun _ ->
            if (pos.(size 0)) >. (shake128_rate *. (nblocks.(size 0))) -. ((size 4) *. nbytes)
            then ( nblocks.(size 0) <- 1ul;
	         let bufSize:size_t = shake128_rate *. (nblocks.(size 0)) in
                 SHA3.cshake128_frodo crypto_randombytes seed (dmsp.(size 0)) (bufSize) buf;
                 dmsp.(size 0) <- UI16.((dmsp.(size 0)) +^ 1us);
                 pos.(size 0) <- 0ul )
            else ();

            let bufSize:size_t = (nblocks.(size 0)) *. shake128_rate in

            let pos0 = pos.(size 0) in
            let subbuff = sub buf pos0 (size (numbytes U32)) in
            let bufPosAsUint = uint_from_bytes_le #U32 #PUB subbuff in
            let val1 = bufPosAsUint &. mask in
            pos.(size 0) <- UI32.(pos0 +^ nbytes);

            let pos0 = pos.(size 0) in
            let subbuff = sub buf pos0 (size (numbytes U32)) in
            let bufPosAsUint = uint_from_bytes_le #U32 #PUB subbuff in
            let val2 = bufPosAsUint &. mask in
            pos.(size 0) <- UI32.(pos0 +^ nbytes);
            
            let pos0 = pos.(size 0) in
            let subbuff = sub buf pos0 (size (numbytes U32)) in
            let bufPosAsUint = uint_from_bytes_le #U32 #PUB subbuff in
            let val3 = bufPosAsUint &. mask in
            pos.(size 0) <- UI32.(pos0 +^ nbytes);

            let pos0 = pos.(size 0) in
            let subbuff = sub buf pos0 (size (numbytes U32)) in
            let bufPosAsUint = uint_from_bytes_le #U32 #PUB subbuff in
            let val4 = bufPosAsUint &. mask in
            pos.(size 0) <- UI32.(pos0 +^ nbytes);

            if (let iVal = i.(size 0) in val1 <. params_q && iVal <. (params_k *. params_n))
            then ( a.(i.(size 0)) <- reduce I64.((uint32_to_int64 val1) *^ params_r2_invn);
                 i.(size 0) <- UI32.((i.(size 0)) +^ 1ul) )
            else ();
            if (let iVal = i.(size 0) in val2 <. params_q && iVal <. (params_k *. params_n))
            then ( a.(i.(size 0)) <- reduce I64.((uint32_to_int64 val2) *^ params_r2_invn);
                 i.(size 0) <- UI32.((i.(size 0)) +^ 1ul) )
            else ();
            if (let iVal = i.(size 0) in val3 <. params_q && iVal <. (params_k *. params_n))
            then ( a.(i.(size 0)) <- reduce I64.((uint32_to_int64 val3) *^ params_r2_invn);
                 i.(size 0) <- UI32.((i.(size 0)) +^ 1ul) )
            else ();
            if (let iVal = i.(size 0) in val4 <. params_q && iVal <. (params_k *. params_n))
            then ( a.(i.(size 0)) <- reduce I64.((uint32_to_int64 val4) *^ params_r2_invn);
                 i.(size 0) <- UI32.((i.(size 0)) +^ 1ul) )
            else ()
        );

    pop_frame()

val ntt:
    a: poly
  -> w: poly
  -> Stack unit
    (requires fun h -> live h a /\ live h w)
    (ensures fun h0 _ h1 -> modifies1 a h0 h1)

let ntt a w =
    push_frame();
    let numoProblems = create (size 1) (params_n >>. (size 1)) in
    let jTwiddle = create (size 1) (size 0) in

    while // Outermost for loop
        #(fun h -> live h numoProblems /\ live h jTwiddle)
        #(fun _ h -> live h numoProblems /\ live h jTwiddle)
        (fun _ -> numoProblems.(size 0) >. (size 0))
        (fun _ ->
            push_frame();
            let j = create (size 1) (size 0) in
            let jFirst = create (size 1) (size 0) in            
            let cond () : Stack bool
              (requires fun h -> live h jFirst)
              (ensures fun h0 _ h1 -> live h1 jFirst)
            = jFirst.(size 0) <. params_n in
            while // Middle for loop
                #(fun h -> live h numoProblems /\ live h jTwiddle /\ live h j /\ live h jFirst)
                #(fun _ h -> live h numoProblems /\ live h jTwiddle /\ live h j /\ live h jFirst)
                cond
                (fun _ ->
                    let jTwiddleVal = jTwiddle.(size 0) in
                    let wj:elem = w.(jTwiddleVal) in
                    jTwiddle.(size 0) <- jTwiddleVal +. (size 1);
                    // Innermost for loop. Have to use a while because the middle for loop's increment depends on the
                    // final value of j from each inner for loop, so its scope can't be constrained to the for loop.
                    j.(size 0) <- jFirst.(size 0);
                    let jFinish:UI32.t = UI32.(jFirst.(size 0) +^ numoProblems.(size 0)) in
                    while
                        #(fun h -> live h numoProblems /\ live h jTwiddle /\ live h jFirst)
                        #(fun _ h -> live h numoProblems /\ live h jTwiddle /\ live h jFirst)
                        (fun _ -> j.(size 0) <. jFinish)
                        (fun _ ->
                            let jVal:size_t = j.(size 0) in
                            let aIndex:size_t = UI32.(jVal +^ numoProblems.(size 0)) in
                            let aVal:elem = a.(aIndex) in
                            let temp:elem = barr_reduce (reduce I64.((elem_to_int64 wj) *^ (elem_to_int64 aVal))) in
                            let aVal:elem = a.(jVal) in
                            a.(aIndex) <- barr_reduce (int64_to_elem I64.((elem_to_int64 aVal) +^ (2L *^ (elem_to_int64 params_q) -^ (elem_to_int64 temp))));
                            a.(jVal) <- barr_reduce (int64_to_elem I64.((elem_to_int64 temp) +^ ((elem_to_int64 aVal))));
			    j.(size 0) <- jVal +. (size 1)
                        );
                    jFirst.(size 0) <- UI32.(j.(size 0) +^ numoProblems.(size 0))
                );
            numoProblems.(size 0) <- UI32.(numoProblems.(size 0) >>^ 1ul);
            pop_frame()
        );
    pop_frame()

// TODO: This implementation varies quite a bit, even between p-I and p-III, which is unusual in what I've found
// so far. Generally the heuristic/provable security division is the differentiator.
val nttinv:
    a: poly
  -> w: poly
  -> Stack unit
    (requires fun h -> live h a /\ live h w)
    (ensures fun h0 _ h1 -> modifies1 a h0 h1)

let nttinv a w =
    push_frame();
    let numoProblems = create (size 1) (size 1) in
    let jTwiddle = create (size 1) (size 0) in

    while // Outermost for loop
        #(fun h -> live h numoProblems /\ live h jTwiddle)
        #(fun _ h -> live h numoProblems /\ live h jTwiddle)
        (fun _ -> numoProblems.(size 0) <. params_n)
        (fun _ ->
            push_frame();
            let j = create (size 1) (size 0) in
            let jFirst = create (size 1) (size 0) in
            let cond () : Stack bool
              (requires fun h -> live h jFirst)
              (ensures fun h0 _ h1 -> live h1 jFirst)
            = jFirst.(size 0) <. params_n in
            while // Middle for loop
                #(fun h -> live h numoProblems /\ live h jTwiddle /\ live h j /\ live h jFirst)
                #(fun _ h -> live h numoProblems /\ live h jTwiddle /\ live h j /\ live h jFirst)
                cond
                (fun _ ->
                    let jTwiddleVal = jTwiddle.(size 0) in
                    let wj:elem = w.(jTwiddleVal) in
                    jTwiddle.(size 0) <- jTwiddleVal +. (size 1);
                    // Innermost for loop. Have to use a while because the middle for loop's increment depends on the
                    // final value of j from each inner for loop, so its scope can't be constrained to the for loop.
                    j.(size 0) <- jFirst.(size 0);
                    let jFinish:UI32.t = UI32.(jFirst.(size 0) +^ numoProblems.(size 0)) in
                    while
                        #(fun h -> live h numoProblems /\ live h jTwiddle /\ live h jFirst)
                        #(fun _ h -> live h numoProblems /\ live h jTwiddle /\ live h jFirst)
                        (fun _ -> j.(size 0) <. jFinish)
                        (fun _ ->
                            let jVal:size_t = j.(size 0) in
                            let aIndex:size_t = UI32.(jVal +^ numoProblems.(size 0)) in
                            let temp:elem = a.(jVal) in
                            let aaIndex:elem = a.(aIndex) in
                            a.(jVal) <- barr_reduce (int64_to_elem I64.((elem_to_int64 temp) +^ (elem_to_int64 aaIndex)));
                            a.(aIndex) <- barr_reduce (reduce I64.((elem_to_int64 wj) *^ ((elem_to_int64 temp) +^ (2L *^ (elem_to_int64 params_q) -^ (elem_to_int64 aaIndex)))));
			    j.(size 0) <- jVal +. (size 1)
                        );
                    jFirst.(size 0) <- UI32.(j.(size 0) +^ numoProblems.(size 0))
                );
            numoProblems.(size 0) <- UI32.(numoProblems.(size 0) *^ 2ul);
            pop_frame()
        );

    pop_frame()

// When the Frodo code creates arrays of constants like this, it uses createL_global, which creates an
// immutable buffer. But this screws up subtyping with poly, which is sometimes mutable. Nik tells us
// there's no good way to do this because, unlike const parameters in C, guarantees like this go both ways
// and we'd essentially be asking the world never to mutate a poly, which is obviously not going to work. So
// we use createL, which makes it mutable, but we just never change it.
let zeta: poly = createL zeta_list

val poly_ntt:
    x_ntt: poly
  -> x: poly
  -> Stack unit
    (requires fun h -> live h x_ntt /\ live h x /\ disjoint x_ntt x)
    (ensures fun h0 _ h1 -> modifies1 x h0 h1)

let poly_ntt x_ntt x =
    push_frame();
    C.Loops.for 0ul params_n
    (fun h _ -> live h x_ntt /\ live h x)
    (fun i ->
        x_ntt.(i) <- (x.(i))
    );

    ntt x_ntt zeta;
    pop_frame()

val poly_pointwise:
    result: poly
  -> x: poly
  -> y: poly
  -> Stack unit
    (requires fun h -> live h result /\ live h x /\ live h y)
    (ensures fun h0 _ h1 -> modifies1 result h0 h1)

let poly_pointwise result x y =
    push_frame();
    C.Loops.for (size 0) params_n
    (fun h _ -> live h result /\ live h x /\ live h y)
    (fun i ->
        let xi:elem = x.(i) in
        let yi:elem = y.(i) in
        result.(i) <- reduce I64.( (elem_to_int64 xi) *^ (elem_to_int64 yi) )
    );
    pop_frame()

// TODO: should call createL_global to make this immutable. Need to work out the typing relationships since poly
// should by default treated as mutable.
let zetainv: poly = createL zetainv_list

val poly_mul:
    result: poly
  -> x: poly
  -> y: poly
  -> Stack unit
    (requires fun h -> live h result /\ live h x /\ live h y)
    (ensures fun h0 _ h1 -> modifies1 result h0 h1)

let poly_mul result x y =
    poly_pointwise result x y;
    nttinv result zetainv;
    ()

val poly_add:
    result: poly
  -> x: poly
  -> y: poly
  -> Stack unit
    (requires fun h -> live h result /\ live h x /\ live h y /\ disjoint result x /\ disjoint result y /\ disjoint x y)
    (ensures fun h0 _ h1 -> modifies1 result h0 h1)

let poly_add result x y =
    push_frame();
    C.Loops.for 0ul params_n
    (fun h _ -> live h result /\ live h x /\ live h y)
    (fun i ->
        result.(i) <- x.(i) +^ y.(i)
    );
    pop_frame()

// TODO: heuristic parameter sets have a poly_add_correct, poly_sub_correct, and poly_sub_reduce

val poly_sub:
    result: poly
  -> x: poly
  -> y: poly
  -> Stack unit
    (requires fun h -> live h result /\ live h x /\ live h y)
    (ensures fun h0 _ h1 -> modifies1 result h0 h1)

let poly_sub result x y =
    push_frame();
    C.Loops.for 0ul params_n
    (fun h _ -> live h result /\ live h x /\ live h y)
    (fun i ->
        let xi:elem = x.(i) in
        let yi:elem = y.(i) in
        result.(i) <- barr_reduce (x.(i) -^ y.(i))
    );
    pop_frame()

val qtesla_keygen:
    pk: buffer uint8
  -> sk: buffer uint8
  -> Stack unit
    (requires fun h -> live h pk /\ live h sk /\ disjoint pk sk)
    (ensures fun h0 _ h1 -> modifies (loc pk |+| loc sk) h0 h1)

// Preliminary work using one of Santiago's loop combinators for the first for loop
(*assume val keygen_sample_spec:
    #rlen:size_nat
  -> rand:Lib.ByteSequence.lbytes rlen
  -> nonce:nat
  -> i:size_nat
  -> e:LibSeq.lseq poly (v params_k)
  -> Tot (LibSeq.lseq poly (v params_k))*)
//let keygen_sample_spec #rlen rand nonce i e ="*)

  (*[@inline_let]
  let spec h0 = keygen_sample_spec (as_seq h0 randomness_extended) (get h0 nonce 0) in
  loop1 h0 (size params_k) e spec
  (fun k ->
    C.Loops.do_while
      (fun h stop -> live h e /\ live h randomness_extended /\
                   (not stop ==> (check_ES (get h e k) params_Le)) /\
                   (stop ==> (not (check_ES (get h e k) params_Le))))
      (fun _ ->
        let nonce0 = nonce.(size 0) in
        nonce.(size 0) <- nonce0 +. 1;
        sample_gauss_poly e.(k) (sub randomness_extended (k * crypto_seedbytes) crypto_randombytes) nonce;
        not (check_ES e.(k) params_Le)));*)

inline_for_extraction noextract private
let randomness_extended_size = (params_k +. size 3) *. crypto_seedbytes

let qtesla_keygen pk sk =
  push_frame();
  let randomness = create crypto_randombytes (u8 0) in
  let randomness_extended = create randomness_extended_size (u8 0) in
  let e:poly_k = poly_k_create () in
  let s:poly = poly_create () in
  let s_ntt:poly = poly_create () in
  let a:poly_k = poly_k_create () in
  let t:poly_k = poly_k_create () in 
  let nonce = create 1ul 0L in
  let mask = create 1ul (to_elem 0) in
  R.randombytes_ crypto_randombytes randomness;
  params_SHAKE crypto_randombytes randomness randomness_extended_size randomness_extended;

  for (size 0) params_k
      (fun h _ -> live h nonce /\ live h e /\ live h randomness_extended)
      (fun k ->
        do_while
          (fun h stop -> live h nonce /\ live h e /\ live h randomness_extended)
                       //(stop ==> (not (check_ES (get_poly e k) params_Le))))
          (fun _ ->
            let subbuffer = sub randomness_extended (k *. crypto_seedbytes) crypto_randombytes in
            let nonce0 = nonce.(size 0) in
            nonce.(size 0) <- I64.(nonce0 +^ 1L);
            let nonce1:uint64 = nonce.(size 0) in
            let ek:poly = index_poly e k in
            sample_gauss_poly ek subbuffer nonce1;
            // TODO: ek is a buffer, and so we shouldn't have to refetch it with index_poly to operate on its current value, right?
            not (check_ES ek params_Le)
          )
      );
  do_while
      (fun h stop -> live h s /\ live h randomness_extended /\ live h nonce)
                   //(stop ==> (not (check_ES s params_Ls)))) // TODO: need Ghost/Tot version of check_ES for invariants
      (fun _ ->
        let rndsubbuffer = sub randomness_extended (params_k *. crypto_seedbytes) crypto_randombytes in
        let nonce0:uint64 = nonce.(size 0) in
        nonce.(size 0) <- nonce0 +. (u64 1);
        let nonce1:uint64 = nonce.(size 0) in
        sample_gauss_poly s rndsubbuffer nonce1;
        not (check_ES s params_Ls)
      );

  let rndsubbuffer = sub randomness_extended ((params_k +. (size 1)) *. crypto_seedbytes) crypto_randombytes in
  poly_uniform a rndsubbuffer;

  // TODO: Heuristic parameter sets call poly_mul and poly_add_correct at this point, which is a poly_add and one type
  // of applied correction. Provable parameter sets (where k > 1, so in a loop) call poly_mul and then poly_add, and
  // apply a different 
  poly_ntt s_ntt s;

  C.Loops.for (size 0) params_k
      (fun h _ -> live h t /\ live h a /\ live h s_ntt /\ live h e /\ live h mask)
      (fun k ->
          let tk:poly = index_poly t k in
          let ak:poly = index_poly a k in
          let ek:poly = index_poly e k in
          poly_mul tk ak s_ntt;
          poly_add tk tk ek;
          C.Loops.for 0ul params_n
          (fun h _ -> live h t /\ live h a /\ live h s_ntt /\ live h e /\ live h mask)
          (fun i ->
              let tki:elem = tk.(i) in
              mask.(size 0) <- (params_q -^ tki) >>^ (size elem_n) -. (size 1);
              let mask0:elem = mask.(size 0) in
              tk.(i) <- tki -^ (params_q &^ mask0)
           )
        );

  encode_or_pack_sk sk s e rndsubbuffer;
  encode_pk pk t rndsubbuffer;

  pop_frame()

val sample_y:
    y : poly
  -> seed : lbuffer uint8 crypto_randombytes
  -> nonce: I32.t
  -> Stack unit
    (requires fun h -> live h y /\ live h seed /\ disjoint y seed)
    (ensures fun h0 _ h1 -> modifies1 y h0 h1)

let sample_y y seed nonce =
    push_frame();

    let nblocks_shake = shake_rate /. (((params_b_bits +. (size 1)) +. (size 7)) /. (size 8)) in
    let bplus1bytes = ((params_b_bits +. size 1) +. (size 7)) /. (size 8) in

    let i = create (size 1) (size 0) in
    let pos = create (size 1) (size 0) in
    let nblocks = create (size 1) params_n in
    let buf = create (params_n *. (((params_b_bits +. size 1) +. (size 7)) /. (size 8)) ) (u8 0) in
    let nbytes = create (size 1) bplus1bytes in
    let dmsp = create (size 1) (int32_to_int16 I32.(nonce <<^ 8ul)) in

    params_cSHAKE crypto_randombytes seed dmsp.(size 0) shake_rate buf;
    dmsp.(size 0) <- I16.(dmsp.(size 0) +^ 1s);

    while
    #(fun h -> live h y /\ live h i /\ live h pos /\ live h nblocks /\ live h buf /\ live h nbytes /\ live h dmsp)
    #(fun _ h -> live h y /\ live h i /\ live h pos /\ live h nblocks /\ live h buf /\ live h nbytes /\ live h dmsp)
    (fun _ -> i.(size 0) <. params_n)
    (fun _ ->
        if (pos.(size 0)) >=. (nblocks.(size 0)) *. (nbytes.(size 0))
	then (
	    nblocks.(size 0) <- nblocks_shake;
	    params_cSHAKE crypto_randombytes seed dmsp.(size 0) shake_rate buf;
	    dmsp.(size 0) <- I16.(dmsp.(size 0) +^ 1s);
	    pos.(size 0) <- size 0
	) else ();

        let pos0 = pos.(size 0) in
	let subbuff = sub buf pos0 (size (numbytes U32)) in
	let bufPosAsU32 = uint_from_bytes_le #U32 #PUB subbuff in
	let bufPosAsElem = uint32_to_elem bufPosAsU32 in
	let i0 = i.(size 0) in
	// TODO: heuristic parameter sets do four at once. Perf?
	y.(i0) <- bufPosAsElem &^ (to_elem 1 <<^ ((params_b_bits +. size 1) -. size 1));
	y.(i0) <- y.(i0) -^ params_B;
	if y.(i0) <> (uint32_to_elem (size 1 <<. params_b_bits))
	then ( i.(size 0) <- i0 +. size 1 )
	else ();
	pos.(size 0) <- pos.(size 0) +. nbytes.(size 0)
    );

    pop_frame()
    

val hash_vm:
    c_bin : buffer uint8
  -> v : poly_k
  -> hm : buffer uint8
  -> Stack unit
    (requires fun h -> live h c_bin /\ live h v /\ live h hm /\ disjoint c_bin v /\ disjoint c_bin hm /\ disjoint v hm)
    (ensures fun h0 _ h1 -> live h1 c_bin /\ live h1 v /\ live h1 hm /\ modifies (loc c_bin) h0 h1)

let hash_vm c_bin v_ hm =
    push_frame();

    let t = create (params_k *. params_n +. crypto_hmbytes) (u8 0) in
    let index = create (size 1) (size 0) in

    for 0ul params_k
    (fun h _ -> live h c_bin /\ live h v_ /\ live h hm)
    (fun k ->
        index.(size 0) <- k *. params_n;
	for 0ul params_n
	(fun h _ -> live h c_bin /\ live h v_ /\ live h hm /\ live h index)
	(fun i ->
	    let temp:elem = v_.(index.(size 0)) in
	    let mask:elem = (params_q /^ (to_elem 2) -^ temp) >>^ (size elem_n) -. (size 1) in
	    let temp:elem = ((temp -^ params_q) &^ mask) |^ (temp &^ (lognot mask)) in
	    let cL:elem = temp &^ (((to_elem 1) <<^ params_d) -^ (to_elem 1)) in
	    let mask:elem = (((to_elem 1) <<^ (params_d -. (size 1))) -^ cL) >>^ (size elem_n) -. (size 1) in
	    let cL:elem = ((cL -^ ((to_elem 1) <<^ params_d)) &^ mask) |^ (cL &^ (lognot mask)) in
	    t.(index.(size 0)) <- elem_to_uint8 ((temp -^ cL) >>^ params_d);
	    // Putting (index.(size 0)) inline in the assignment causes a typing error for some reason.
	    // Opened a bug on this.
	    let indexVal:size_t = index.(size 0) in
	    index.(size 0) <- indexVal +. (size 1)
	)
    );

    update_sub #MUT #_ #_ t (params_k *. params_n) crypto_hmbytes hm;
    params_SHAKE (params_k *. params_n +. crypto_hmbytes) t crypto_c_bytes c_bin;

    pop_frame()


val encode_c:
    pos_list : lbuffer UI32.t params_h
  -> sign_list : lbuffer I16.t params_h
  -> c_bin : buffer uint8
  -> Stack unit
    (requires fun h -> live h pos_list /\ live h sign_list /\ live h c_bin /\ disjoint pos_list sign_list /\
                    disjoint pos_list c_bin /\ disjoint sign_list c_bin)
    (ensures fun h0 _ h1 -> live h1 pos_list /\ live h1 sign_list /\ live h1 c_bin /\ modifies2 pos_list sign_list h0 h1)

// This function looks identical between the I and p-III sets.
let encode_c pos_list sign_list c_bin =
    push_frame();

    let c = create params_n 0s in
    let r = create shake128_rate (u8 0) in
    let dmsp = create (size 1) (u16 0) in
    let cnt = create (size 1) (size 0) in
    let i = create (size 1) (size 0) in

    SHA3.cshake128_frodo crypto_randombytes c_bin (dmsp.(size 0)) shake128_rate r;
    let dmspVal:uint16 = dmsp.(size 0) in
    dmsp.(size 0) <- dmspVal +. (u16 1);

    // c already initialized to zero above, no need to loop and do it again

    while
    #(fun h -> live h pos_list /\ live h sign_list /\ live h c_bin /\ live h c /\ live h r /\ live h dmsp)
    #(fun _ h -> live h pos_list /\ live h sign_list /\ live h c_bin /\ live h c /\ live h r /\ live h dmsp)
    (fun _ -> (i.(size 0)) <. params_h)
    (fun _ ->
        let iVal:size_t = i.(size 0) in
	let cntVal:size_t = cnt.(size 0) in
        if cntVal >. (shake128_rate -. (size 3))
	then ( SHA3.cshake128_frodo crypto_randombytes c_bin (dmsp.(size 0)) shake128_rate r;
	       let dmspVal:uint16 = dmsp.(size 0) in
	       dmsp.(size 0) <- dmspVal +. (u16 1)
	     )
	else ();

        let rCntVal:uint8 = r.(cntVal) in
	let pos:size_t = (rCntVal <<. (size 8)) |. (r.(cntVal +. (size 1))) in
	let pos:size_t = pos &. (params_n -. (size 1)) in

	if (c.(pos)) = 0s
	then ( if (r.(cntVal +. (size 2)) &. 1y) = 1y
	       then c.(pos) <- -1s
	       else c.(pos) <- 1s;
	       pos_list.(iVal) <- pos;
	       sign_list.(iVal) <- c.(pos);
	       i.(size 0) <- iVal +. (size 1)
	     )
	else ();
	cnt.(size 0) <- cntVal +. (size 3)
    );

    pop_frame()

val sparse_mul8:
    prod : poly
  -> sk : lbuffer uint8 crypto_secretkeybytes
  -> pos_list : lbuffer UI32.t params_h
  -> sign_list : lbuffer I16.t params_h
  -> Stack unit
    (requires fun h -> live h prod /\ live h sk /\ live h pos_list /\ live h sign_list /\ disjoint prod sk /\ disjoint prod pos_list /\ disjoint prod sign_list)
    (ensures fun h0 _ h1 -> live h1 prod /\ live h1 sk /\ live h1 pos_list /\ live h1 sign_list /\ modifies1 prod h0 h1)

let sparse_mul8 prod sk pos_list sign_list =
    push_frame();

    let t = sk in
    
    for 0ul params_n
    (fun h _ -> live h prod)
    (fun i -> prod.(i) <- to_elem 0);

    for 0ul params_h
    (fun h _ -> live h prod /\ live h sk /\ live h pos_list /\ live h sign_list)
    (fun i ->
        let pos = pos_list.(i) in
	for 0ul pos
	(fun h _ -> live h prod /\ live h sk /\ live h pos_list /\ live h sign_list)
	(fun j -> 
	    let sign_list_i:I16.t = sign_list.(i) in
	    let tVal:uint8 = t.(j +. params_n -. pos) in
	    prod.(j) <- (prod.(j)) -^ (int16_to_elem I16.(sign_list_i *^ (uint8_to_int16 tVal)))
	);

	for pos params_n
	(fun h _ -> live h prod /\ live h sk /\ live h pos_list /\ live h sign_list)
	(fun j -> 
	    let sign_list_i:I16.t = sign_list.(i) in
	    let tVal:uint8 = t.(j -. pos) in
  	    prod.(j) <- (prod.(j)) +^ (int16_to_elem I16.(sign_list_i *^ (uint8_to_int16 tVal)))
	)
    );

    pop_frame()

val sparse_mul32:
    prod : poly
  -> pk : lbuffer I32.t params_n
  -> pos_list : lbuffer UI32.t params_h
  -> sign_list : lbuffer I16.t params_h
  -> Stack unit
    (requires fun h -> live h prod /\ live h pk /\ live h pos_list /\ live h sign_list)
    (ensures fun h0 _ h1 -> modifies1 prod h0 h1)

let sparse_mul32 prod pk pos_list sign_list =
    push_frame();

    for 0ul params_n
    (fun h _ -> live h prod /\ live h pk /\ live h pos_list /\ live h sign_list)
    (fun i -> prod.(i) <- to_elem 0);

    for 0ul params_h
    (fun h _ -> live h prod /\ live h pk /\ live h pos_list /\ live h sign_list)
    (fun i ->
        let pos = pos_list.(i) in
	let sign_list_i = sign_list.(i) in
	for 0ul pos
	(fun h _ -> live h prod /\ live h pk /\ live h pos_list /\ live h sign_list)
	(fun j ->
	    let pkItem = pk.(j +. params_n -. pos) in
	    prod.(j) <- (prod.(j)) -^ int32_to_elem I32.( (int16_to_int32 sign_list_i) *^ pkItem )
	);
	for pos params_n
	(fun h _ -> live h prod /\ live h pk /\ live h pos_list /\ live h sign_list)
	(fun j ->
	    let pkItem = pk.(j -. pos) in
	    prod.(j) <- (prod.(j)) +^ int32_to_elem I32.( (int16_to_int32 sign_list_i) *^ pkItem )
	)
    );

    for 0ul params_n
    (fun h _ -> live h prod /\ live h pk /\ live h pos_list /\ live h sign_list)
    (fun i -> prod.(i) <- barr_reduce (prod.(i)));

    pop_frame()

val test_rejection:
    z : poly
  -> Stack bool
    (requires fun h -> live h z)
    (ensures fun h0 _ h1 -> h0 == h1)

let test_rejection z =
    push_frame();

    let _, res =
    interruptible_for 0ul params_n
    (fun h _ _ -> live h z)
    (fun i ->
        let zVal = z.(i) in
	(abs_elem zVal) >^ (params_B -^ params_U)
    ) in

    pop_frame();
    res

val test_v:
    v : poly
  -> Stack I32.t
    (requires fun h -> live h v)
    (ensures fun h0 _ h1 -> h0 == h1)

let test_v v =
    push_frame();

    let res = create (size 1) 0l in

    let _, _ = interruptible_for 0ul params_n
    (fun h _ _ -> live h v)
    (fun i ->
        let mask:elem = (params_q /^ (to_elem 2) -^ (v.(i))) >>^ (size elem_n) -. (size 1) in
	let val_:elem = ((v.(i) -^ params_q) &^ mask) |^ (v.(i) &^ (lognot mask)) in
	// TODO: t0 and t1 are the unsigned type of the element type. Important?
	let t0 = (lognot ((abs_elem val_) -^ (params_q /^ (size 2) -^ params_rejection))) >>^ (size elem_n) -. (size 1) in
	let left = val_ in
	// TODO: in the ref code, this computation of val is cast to int32_t. Not sure why.
	let val_:elem = (val_ +^ ((to_elem 1) <<^ (params_d -. (size 1))) -^ (to_elem 1)) >>^ params_d in
	let val_:elem = left -^ (val_ <<^ params_d) in
	let t1 = (lognot ((abs_elem val_) -^ ((to_elem 1) <<^ (params_d -. (size 1))) -^ params_rejection)) >>^ (size elem_n) -. (size 1) in
        if (t0 |^ t1) = to_elem 1
	then ( res.(size 0) <- 1l; true )
	else ( false )
    ) in

    let resVal:I32.t = res.(size 0) in
    pop_frame();
    resVal
    

val qtesla_sign:
    smlen : lbuffer size_t 1ul // smlen only valid on output; does _not_ indicate allocated size of sm on input
  -> m : buffer uint8
  -> mlen : size_t{B.length m = v mlen}
  -> sm: lbuffer uint8 (crypto_bytes +. mlen)
  -> sk : lbuffer uint8 crypto_secretkeybytes
  -> Stack unit
    (requires fun h -> live h sm /\ live h m /\ live h sk /\ disjoint sm m /\ disjoint sm sk /\ disjoint m sk)
    (ensures fun h0 _ h1 -> live h1 sm /\ live h1 m /\ live h1 sk /\ modifies (loc sm |+| loc smlen) h0 h1)
    //modifies2 sm smlen h0 h1)

let qtesla_sign smlen m mlen sm sk =
    push_frame();

    let c = create crypto_c_bytes (u8 0) in
    let randomness = create crypto_seedbytes (u8 0) in
    let randomness_input = create (crypto_randombytes +. crypto_seedbytes +. crypto_hmbytes) (u8 0) in
    let pos_list = create params_h (UI32.uint_to_t 0) in
    let sign_list = create params_h (I16.int_to_t 0) in
    let y:poly = poly_create () in
    let y_ntt:poly = poly_create () in
    let sc:poly = poly_create () in
    let z:poly = poly_create () in 
    let v_:poly_k = poly_k_create () in 
    let ec:poly_k = poly_k_create () in
    let a:poly_k = poly_k_create () in
    let rsp = create (size 1) (I32.int_to_t 0) in
    let nonce = create (size 1) (I32.int_to_t 0) in

    // TODO: decode_sk here in heuristic parameter sets. I think this may just be relocating the pointer arithmetic
    // that happens inline in the provable parameter sets.

    R.randombytes_ crypto_randombytes (sub randomness_input crypto_randombytes crypto_randombytes);
    update_sub randomness_input (size 0) crypto_seedbytes (sub sk (crypto_secretkeybytes -. crypto_seedbytes) crypto_seedbytes);
    params_SHAKE mlen m crypto_hmbytes (sub randomness_input (crypto_randombytes +. crypto_seedbytes) crypto_hmbytes);
    params_SHAKE (crypto_randombytes +. crypto_seedbytes +. crypto_hmbytes) randomness_input crypto_seedbytes randomness;

    poly_uniform a (sub #_ #_ #(v crypto_randombytes) sk (crypto_secretkeybytes -. (size 2) *. crypto_seedbytes) crypto_randombytes);

    do_while
        (fun h _ -> live h c /\ live h randomness /\ live h randomness_input /\
                     live h pos_list /\ live h sign_list /\ live h y /\ live h y_ntt /\ live h sc /\ live h z /\
                     live h v_ /\ live h ec /\ live h a /\ live h rsp /\ live h nonce /\ live h sm /\ live h m /\ live h sk)
        (fun _ ->
            nonce.(size 0) <- I32.(nonce.(size 0) +^ 1l);
            sample_y y randomness (nonce.(size 0));
	    // TODO: ntt transformation only happens here in provable parameter sets because poly_mul assumes
	    // both arguments are in ntt form. Heuristic parameter sets only assume the first parameter is in
	    // ntt form.
            poly_ntt y_ntt y;
            for 0ul params_k
                (fun h _ -> live h c /\ live h randomness /\  live h randomness_input /\
                     live h pos_list /\ live h sign_list /\ live h y /\ live h y_ntt /\ live h sc /\ live h z /\
                     live h v_ /\ live h ec /\ live h a /\ live h rsp /\ live h nonce /\ live h sm /\ live h m /\ live h sk)
                (fun k ->
                    poly_mul (index_poly v_ k) (index_poly a k) y_ntt
                );

            hash_vm c v_ (sub randomness_input (crypto_randombytes +. crypto_seedbytes) crypto_hmbytes);
            encode_c pos_list sign_list c;
	    // TODO: heuristic parameter sets use sparse_mul16
            sparse_mul8 sc sk pos_list sign_list;
            poly_add z y sc;

            if test_rejection z
            then (false)
            else (
                 push_frame();
                 let k = create (size 1) (size 0) in
                 let stop = create (size 1) false in
                 while
                 #(fun h -> live h c /\ live h randomness /\  live h randomness_input /\
                     live h pos_list /\ live h sign_list /\ live h y /\ live h y_ntt /\ live h sc /\ live h z /\
                     live h v_ /\ live h ec /\ live h a /\ live h rsp /\ live h nonce /\ live h sm /\ live h m /\ live h sk /\ live h k /\ live h stop)
                 #(fun _ h -> live h c /\ live h randomness /\  live h randomness_input /\
                     live h pos_list /\ live h sign_list /\ live h y /\ live h y_ntt /\ live h sc /\ live h z /\
                     live h v_ /\ live h ec /\ live h a /\ live h rsp /\ live h nonce /\ live h sm /\ live h m /\ live h sk /\ live h k /\ live h stop)
                 // See https://github.com/FStarLang/FStar/issues/1579
                 (fun () -> (* k.(size 0) <. params_k && *) not stop.(size 0))
                 (fun _ ->
                     let kVal:size_t = k.(size 0) in
		     if (kVal <. params_k)
		     then (
                         let sk_offset:size_t = (params_n *. (kVal +. (size 1))) in
                         let sublen:size_t = crypto_secretkeybytes -. sk_offset in
			 // TODO: heuristic parameter sets use sparse_mul16
                         sparse_mul8 (index_poly ec kVal) (sub #_ #_ #(v sublen) sk sk_offset sublen) pos_list sign_list;
                         poly_sub (index_poly v_ kVal) (index_poly v_ kVal) (index_poly ec kVal);
                         rsp.(size 0) <- test_v (index_poly v_ kVal);
                         if (let rspVal = rsp.(size 0) in not (rspVal = 0l))
                         then ( stop.(size 0) <- true )
                         else ( k.(size 0) <- (k.(size 0)) +. (size 1) ) )
	             else ( stop.(size 0) <- true )
                 );
                 pop_frame();

                 if (let rspVal = rsp.(size 0) in not (rspVal = 0l))
                 then (false)
                 else (
                      for 0ul mlen
                      (fun h _ -> live h c /\ live h randomness /\  live h randomness_input /\
                     live h pos_list /\ live h sign_list /\ live h y /\ live h y_ntt /\ live h sc /\ live h z /\
                     live h v_ /\ live h ec /\ live h a /\ live h rsp /\ live h nonce /\ live h sm /\ live h m /\ live h sk)
                      (fun i -> sm.(crypto_bytes +. i) <- B.index m i );

                      smlen.(size 0) <- crypto_bytes +. mlen;

                      encode_sig sm c z;

                      true
                      )
                )
           );
    pop_frame()

val test_z:
    z : poly
  -> Stack I32.t
    (requires fun h -> live h z)
    (ensures fun h0 _ h1 -> h0 == h1)

let test_z z =
    let _ , res = interruptible_for 0ul params_n
    (fun h _ _ -> live h z)
    (fun i ->
        let zi = z.(i) in
	zi <^ to_elem (-1) *^ (params_B -^ params_U) || zi >^ (params_B -^ params_U)
    ) in
    if res
    then 1l
    else 0l

val qtesla_verify:
    mallocated : size_t
  -> mlen : lbuffer size_t 1ul
  -> m : lbuffer uint8 mallocated
  -> smlen : size_t
  -> sm : lbuffer uint8 smlen
  -> pk : lbuffer uint8 crypto_publickeybytes
  -> Stack I32.t
    (requires fun h -> live h m /\ live h sm /\ live h pk)
    (ensures fun h0 _ h1 -> modifies2 mlen m h0 h1)

let qtesla_verify mallocated mlen m smlen sm pk =

    // Can't return from the middle of a function in F*, so instead we use this if-then-else structure where
    // the else is the entire rest of the function after the return statement.
    if smlen <. crypto_bytes then ( -1l ) else (
    push_frame();
    let c = create crypto_c_bytes (u8 0) in
    let c_sig = create crypto_c_bytes (u8 0) in
    let seed = create crypto_seedbytes (u8 0) in
    let hm = create crypto_hmbytes (u8 0) in
    let pos_list = create params_h 0ul in
    let sign_list = create params_h 0s in
    let pk_t = create (params_n *. params_k) 0l in
    let w = poly_k_create () in
    let a = poly_k_create () in
    let tc = poly_k_create () in
    let z = poly_create () in
    let z_ntt = poly_create() in

    decode_sig c z smlen sm;
    if test_z z <> 0l then ( pop_frame(); -2l ) else (
    decode_pk pk_t seed pk;
    poly_uniform a seed;
    encode_c pos_list sign_list c;
    poly_ntt z_ntt z;

    for 0ul params_k
    (fun h _ -> live h w /\ live h a /\ live h z_ntt /\ live h tc /\ live h pk_t /\ live h pos_list /\ live h sign_list)
    (fun k ->
        poly_mul (index_poly w k) (index_poly a k) z_ntt;
	sparse_mul32 (index_poly tc k) (sub pk_t (k *. params_n) params_n) pos_list sign_list;
	// TODO: heuristic parameter sets use poly_sub_reduce
	poly_sub (index_poly w k) (index_poly w k) (index_poly tc k)
    );

    params_SHAKE (smlen -. crypto_bytes) (sub sm crypto_bytes (smlen -. crypto_bytes)) crypto_hmbytes hm;
    hash_vm c_sig w hm;

    // lbytes_eq iterates over the entire buffer no matter what, which we don't need. memcmp would be fine since
    // this is all public data. Not yet determined if there's a construct which extracts as memcmp.
    // So we may do unnecessary work but it's still correct.
    if not (lbytes_eq c c_sig) then ( pop_frame(); -3l ) else (
    let mlenVal = smlen -. crypto_bytes in
    mlen.(size 0) <- mlenVal;
    for 0ul mlenVal
    (fun h _ -> live h m /\ live h sm)
    (fun i -> m.(i) <- sm.(crypto_bytes +. i) );

    pop_frame();
    0l
    )))

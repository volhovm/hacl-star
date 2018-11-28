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
//open Lib.ByteBuffer

open C.Loops

open Hacl.Impl.QTesla.Params

module B  = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack

module Seq = FStar.Seq
module LibSeq = Lib.Sequence

module FS   = Spec.SHA3
module SHA3 = Hacl.SHA3
module S    = Spec.QTesla

module R    = Hacl.QTesla.Random

type poly = lbuffer elem (v params_n)
type poly_k = lbuffer elem (v (params_k *. params_n))

//unfold let create_poly _ : poly = create #_ #params_n (size params_n) (to_elem 0)
//unfold let create_polys_k _ : poly_k = create #_ #(params_n * params_k) (size (params_n * params_k)) (to_elem 0)

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --admit_smt_queries true"

val get_poly: p: poly_k -> k: size_t{k <. params_k} -> GTot poly
let get_poly p k = gsub p (k *. params_n) params_n

val index_poly: p: poly_k -> k: size_t{k <. params_k} -> Stack poly
    (requires fun h -> live h p)
    (ensures fun h0 pk h1 -> h0 == h1 /\ pk == get_poly p k)
let index_poly p k = sub p (k *. params_n) params_n

let randomness_extended_size = normalize_term ((params_k +. size 3) *. crypto_seedbytes)

assume val cshake128_frodo:
    input_len:size_t
  -> input:lbuffer uint8 (v input_len)
  -> cstm:uint16
  -> output_len:size_t
  -> output: lbuffer uint8 (v output_len)
  -> Stack unit
    (requires fun h -> live h input /\ live h output /\ disjoint input output)
    (ensures fun h0 _ h1 ->
      modifies1 output h0 h1 /\
      as_seq h1 output == FS.cshake128_frodo (v input_len) (as_seq h0 input) cstm (v output_len))

val cdtIndex:
    x : size_t
  -> y : size_t
  -> Tot size_t

// TODO: Will need for implementation of sample_gauss_poly
(*let cdtIndex x y = x *. (size 3) + y*)

assume val sample_gauss_poly:
    x: poly
  -> seed: lbuffer uint8 (v crypto_randombytes)
  -> nonce: FStar.Int64.t
  -> Stack unit
    (requires fun h -> live h x /\ live h seed /\ disjoint x seed)
    (ensures fun h0 _ h1 ->
      live h1 x /\ live h1 seed /\
      modifies1 x h0 h1) // TODO: output equal to spec

// TODO: There is all kinds of specialized per-parameter-set stuff happening in sample_gauss_poly.
// Need to figure out how to write a more general parameterized implementation, or if it's necessary,
// write a separate one for each parameter set.
(*let sample_gauss_poly x seed nonce =
    [@inline_let]
    let cdtList: list I64.t = [
    0x0000020000000000L; 0x0000000000000000L; 0x0000000000000000L;
    0x0000030000000000L; 0x0000000000000000L; 0x0000000000000000L;
    0x0000032000000000L; 0x0000000000000000L; 0x0000000000000000L;
    0x0000032100000000L; 0x0000000000000000L; 0x0000000000000000L;
    0x0000032102000000L; 0x0000000000000000L; 0x0000000000000000L;
    0x0000032102010000L; 0x0000000000000000L; 0x0000000000000000L;
    0x0000032102010020L; 0x0000000000000000L; 0x0000000000000000L;
    0x0000032102010020L; 0x0100000000000000L; 0x0000000000000000L;
    0x0000032102010020L; 0x0100020000000000L; 0x0000000000000000L;
    0x0000032102010020L; 0x0100020001000000L; 0x0000000000000000L;
    0x0000032102010020L; 0x0100020001000020L; 0x0000000000000000L;
    0x0000032102010020L; 0x0100020001000020L; 0x0001000000000000L;
    0x0000032102010020L; 0x0100020001000020L; 0x0001000002000000L;
    0x0000032102010020L; 0x0100020001000020L; 0x0001000002000001L ] in
    let cdt = createL_global cdtList in
    push_frame();

    let seed_ex = create #uint8 #(v params_n * 8) (params_n *. (size 8)) (u8 0) in
    let j = create #I64.t #1 (size 1) 0L in
    let bitsremained = create #I64.t #1 (size 1) 0L in
    let rbits = create #I64.t #1 (size 1) 0L in
    let y = create #I64.t #1
    let r = create #UI64.t #1 (size 1) 0uL in
    let s = create #UI64.t #1 (size 1) 0uL in
    let t = create #UI64.t #1 (size 1) 0uL in
    let c = create #UI64.t #1 (size 1) 0uL in

    params_gaussSampler_xof crypto_randombytes seed dmsp.(size 0) (params_n *. (size 8)) buf;

    let buf = bufferAsInt64s seed_ex in

    for 0ul params_n
        (fun h _ -> live h seed_ex /\ live h j)
        (fun x_ind ->
            if let jVal = j.size(0) in jVal +. 46 >. params_n
            then ( params_gaussSampler_xof crypto_randombytes seed dmsp.(size 0) (params_n *. (size 8)) buf;
                   j.(size 0) <- (size 0)
                 )
            else ();

            do_while
                (fun h _ -> live h seed_ex /\ live h buf /\ live h j)
                (fun _ ->
                    rbits.(size 0) <- buf.(j.(size 0));
                    j.(size 0) <- j.(size 0) +. (size 1);
                    bitsremained.(size 0) <- 64L;

                    do_while
                        (fun h -> live h seed_ex /\ live h buf /\ live h j)
                        (fun _ ->
                            r.(size 0) <- buf.(j.(size 0));
                            j.(size 0) <- I64.((j.(size 0)) +^ 1L);
                            s.(size 0) <- buf.(j.(size 0));
                            j.(size 0) <- I64.((j.(size 0)) +^ 1L);
                            t.(size 0) <- buf.(j.(size 0));
                            j.(size 0) <- I64.((j.(size 0)) +^ 1L);
                            if (let bitsremainedVal = bitsremainedVal.(size 0) in bitsremainedVal <=^ 64L - 6L)
                            then rbits.(size 0) <- I64.t(((rbits.(size 0)) <<^ 6L) ^^ (((r.(size 0)) >>^ 58L) &^ 63L))
                            else ();
                            r.(size 0) <- I64.t(r.(size 0) &^ 0x000003FFFFFFFFFFL);

                            I64.t(r.(size 0) >^ 0x0000032102010020L)
                        );

                    y.(size 0) <- 0L;*)


val sampleE_state: i:size_nat -> Type0
let sampleE_state i = tuple2 S.polys_t S.positive

// TODO: Better way of doing negation/absolute value of an Int64?
val abs_elem: elem -> elem
let abs_elem x = if x <^ (to_elem 0) then x *^ (to_elem (-1)) else x

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
        list.(j) <- elem_to_int16 abspj);

  for (size 0) params_h
      (fun h _ -> live h p /\ live h sum /\ live h limit /\ live h temp /\ live h mask /\ live h list)
      (fun j ->
          let loopMax:UI32.t = UI32.((limit.(0ul)) -^ 1ul) in
          for 0ul loopMax
          (fun h _ -> live h p /\ live h sum /\ live h limit /\ live h temp /\ live h mask /\ live h list)
          (fun i32 ->
              let i = uint32_to_int16 i32 in
              mask.(size 0) <- I16.( (list.(i +^ 1s)) -^ (list.(i)) >>^ 15ul );
              temp.(size 0) <- I16.(( (list.(i +^ 1s)) &^ (mask.(0ul)) ) |^
                              ( (list.(i)) &^ (lognot mask.(size 0)) ));
              list.(I16.(i +^ 1s)) <- I16.(( (list.(i)) &^ mask.(0ul) ) |^
                                         ( (list.(i +^ 1s)) &^ (lognot mask.(0ul)) ));
              list.(i) <- temp.(size 0)
          );

          let listIndex:UI32.t = UI32.((limit.(0ul)) -^ 1ul) in
          let listAmt:I16.t = list.(listIndex) in
          let listAmt:UI32.t = int16_to_uint32 listAmt in
          sum.(size 0) <- UI32.(sum.(size 0) +^ listAmt);
          limit.(size 0) <- UI32.((limit.(size 0)) -^ 1ul)
      );

   let sumAmt:UI32.t = sum.(0ul) in
   let res = UI32.(sumAmt >^ bound) in
   pop_frame();
   res

unfold let shake128_rate:size_t = size 168

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
  -> seed: lbuffer uint8 (v crypto_randombytes)
  -> Stack unit
    (requires fun h -> live h a /\ live h seed /\ disjoint a seed)
    (ensures fun h0 _ h1 -> live h1 a /\ live h1 seed /\ modifies1 a h0 h1)

let poly_uniform a seed =
    push_frame();
    let pos = create (size 1) (size 0) in
    let i = create (size 1) (u32 0) in
    let nbytes:size_t = (params_q_log +. 7ul) /. 8ul in
    let nblocks = create (size 1) params_genA in
    let mask:UI32.t = (1ul <<. params_q_log) -. 1ul in
    let bufSize:size_t = nblocks.(0ul) *. shake128_rate in
    let buf = create bufSize (u8 0) in
    let dmsp = create (size 1) 0us in
    cshake128_frodo crypto_randombytes seed (dmsp.(0ul)) bufSize buf;
    dmsp.(0ul) <- UI16.((dmsp.(0ul)) +^ 1us);

    while
        #(fun h -> live h pos /\ live h i /\ live h nblocks /\ live h buf /\ live h dmsp)
        #(fun _ h -> live h pos /\ live h i /\ live h nblocks /\ live h buf /\ live h dmsp)
        ( fun _ -> (i.(0ul)) <. (params_k *. params_n) )
        ( fun _ ->
            let bufSize:size_t = (nblocks.(0ul)) *. shake128_rate in
            if (pos.(0ul)) >. bufSize -. (4ul *. nbytes)
            then ( nblocks.(0ul) <- 1ul;
                 let bufSize:size_t = (nblocks.(0ul)) *. shake128_rate in
                 cshake128_frodo crypto_randombytes seed (dmsp.(0ul)) bufSize buf;
                 dmsp.(0ul) <- UI16.((dmsp.(0ul)) +^ 1us);
                 pos.(0ul) <- 0ul )
            else ();

            let bufSize:size_t = (nblocks.(0ul)) *. shake128_rate in

            let pos0 = pos.(0ul) in
            let subbuff = sub buf pos0 (size (numbytes U32)) in
            let bufPosAsUint = uint_from_bytes_le #U32 #PUB subbuff in
            let val1 = bufPosAsUint &. mask in
            pos.(0ul) <- UI32.(pos0 +^ nbytes);

            let pos0 = pos.(0ul) in
            let subbuff = sub buf pos0 (size (numbytes U32)) in
            let bufPosAsUint = uint_from_bytes_le #U32 #PUB subbuff in
            let val2 = bufPosAsUint &. mask in
            pos.(0ul) <- UI32.(pos0 +^ nbytes);
            
            let pos0 = pos.(0ul) in
            let subbuff = sub buf pos0 (size (numbytes U32)) in
            let bufPosAsUint = uint_from_bytes_le #U32 #PUB subbuff in
            let val3 = bufPosAsUint &. mask in
            pos.(0ul) <- UI32.(pos0 +^ nbytes);

            let pos0 = pos.(0ul) in
            let subbuff = sub buf pos0 (size (numbytes U32)) in
            let bufPosAsUint = uint_from_bytes_le #U32 #PUB subbuff in
            let val4 = bufPosAsUint &. mask in
            pos.(0ul) <- UI32.(pos0 +^ nbytes);

            if (let iVal = i.(0ul) in val1 <. params_q && iVal <. (params_k *. params_n))
            then ( a.(i.(0ul)) <- reduce I64.((uint32_to_int64 val1) *^ params_r2_invn);
                 i.(0ul) <- UI32.((i.(0ul)) +^ 1ul) )
            else ();
            if (let iVal = i.(0ul) in val2 <. params_q && iVal <. (params_k *. params_n))
            then ( a.(i.(0ul)) <- reduce I64.((uint32_to_int64 val2) *^ params_r2_invn);
                 i.(0ul) <- UI32.((i.(0ul)) +^ 1ul) )
            else ();
            if (let iVal = i.(0ul) in val3 <. params_q && iVal <. (params_k *. params_n))
            then ( a.(i.(0ul)) <- reduce I64.((uint32_to_int64 val3) *^ params_r2_invn);
                 i.(0ul) <- UI32.((i.(0ul)) +^ 1ul) )
            else ();
            if (let iVal = i.(0ul) in val4 <. params_q && iVal <. (params_k *. params_n))
            then ( a.(i.(0ul)) <- reduce I64.((uint32_to_int64 val4) *^ params_r2_invn);
                 i.(0ul) <- UI32.((i.(0ul)) +^ 1ul) )
            else ()
        );

    pop_frame()

// TODO: zeta varies per parameter set
assume val zeta: poly

val ntt:
    a: poly
  -> w: poly
  -> Stack unit
    (requires fun h -> live h a /\ live h w)
    (ensures fun h0 _ h1 -> live h1 a /\ live h1 w /\ modifies1 a h0 h1)

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
            = true in //jFirst.(size 0) <. params_n in
            while // Middle for loop
                #(fun h -> live h numoProblems /\ live h jTwiddle /\ live h j /\ live h jFirst)
                #(fun _ h -> live h numoProblems /\ live h jTwiddle /\ live h j /\ live h jFirst)
                cond
                (fun _ -> ());
                (*
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
                            a.(j) <- barr_reduce (int64_to_elem I64.((elem_to_int64 temp) +^ ((elem_to_int64 aVal))))
                        );
                    jFirst.(size 0) <- UI32.(j.(size 0) +^ numoProblems.(size 0))
                );*)
            numoProblems.(size 0) <- UI32.(numoProblems.(size 0) >>^ 1ul);
            pop_frame()
        );
    pop_frame()

val nttinv:
    a: poly
  -> w: poly
  -> Stack unit
    (requires fun h -> live h a /\ live h w)
    (ensures fun h0 _ h1 -> live h1 a /\ live h1 w /\ modifies1 a h0 h1)

let nttinv a w =
    push_frame();
    let numoProblems = create (size 1) (size 1) in
    let jTwiddle = create (size 1) (size 0) in

    C.Loops.while // Outermost for loop
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
            = true in //jFirst.(size 0) <. params_n in
            C.Loops.while // Middle for loop
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
                    C.Loops.while
                        #(fun h -> live h numoProblems /\ live h jTwiddle /\ live h jFirst)
                        #(fun _ h -> live h numoProblems /\ live h jTwiddle /\ live h jFirst)
                        (fun _ -> j.(size 0) <. jFinish)
                        (fun _ ->
                            let jVal:size_t = j.(size 0) in
                            let aIndex:size_t = UI32.(jVal +^ numoProblems.(size 0)) in
                            let temp:elem = a.(j) in
                            let aaIndex:elem = a.(aIndex) in
                            a.(j) <- barr_reduce (int64_to_elem I64.((elem_to_int64 temp) +^ (elem_to_int64 aaIndex)));
                            a.(aIndex) <- barr_reduce (reduce I64.((elem_to_int64 wj) *^ ((elem_to_int64 temp) +^ (2L *^ (elem_to_int64 params_q) -^ (elem_to_int64 aaIndex)))))
                        );
                    jFirst.(size 0) <- UI32.(j.(size 0) +^ numoProblems.(size 0))
                );
            numoProblems.(size 0) <- UI32.(numoProblems.(size 0) *^ 2ul);
            pop_frame()
        );

    pop_frame()

val poly_ntt:
    x_ntt: poly
  -> x: poly
  -> Stack unit
    (requires fun h -> live h x_ntt /\ live h x /\ disjoint x_ntt x)
    (ensures fun h0 _ h1 -> live h1 x_ntt /\ live h1 x /\ modifies1 x h0 h1)

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
    (ensures fun h0 _ h1 -> live h1 result /\ live h1 x /\ live h1 y /\ modifies1 result h0 h1)

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

val poly_mul:
    result: poly
  -> x: poly
  -> y: poly
  -> Stack unit
    (requires fun h -> live h result /\ live h x /\ live h y)
    (ensures fun h0 _ h1 -> live h1 result /\ live h1 x /\ live h1 y /\ modifies1 result h0 h1)

// TODO
assume val zetainv: poly

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
    (ensures fun h0 _ h1 -> live h1 result /\ live h1 x /\ live h1 y /\ modifies1 result h0 h1)

let poly_add result x y =
    push_frame();
    C.Loops.for 0ul params_n
    (fun h _ -> live h result /\ live h x /\ live h y)
    (fun i ->
        result.(i) <- x.(i) +^ y.(i)
    );
    pop_frame()

val poly_sub:
    result: poly
  -> x: poly
  -> y: poly
  -> Stack unit
    (requires fun h -> live h result /\ live h x /\ live h y)
    (ensures fun h0 _ h1 -> live h1 result /\ live h1 x /\ live h1 y /\ modifies1 result h0 h1)

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

// TODO: All the pack.c functions (pack_sk, encode_pk, decode_pk, encode_sig, decode_sig) are very tied to their
// parameter sets. Until we have the project set up to do per-parameter set implementations, assume these functions.
assume val pack_sk:
    sk: lbuffer uint8 (v crypto_secretkeybytes)
  -> s: poly
  -> e: poly_k
  -> seeds: lbuffer uint8 (2 * (v crypto_seedbytes))
  -> Stack unit
    (requires fun h -> live h sk /\ live h s /\ live h e /\ live h seeds /\
                    disjoint sk s /\ disjoint sk e /\ disjoint sk seeds /\
                    disjoint s e /\ disjoint s seeds /\ disjoint e seeds)
    (ensures fun h0 _ h1 -> modifies1 sk h0 h1)

(*let pack_sk sk s e seeds =
    push_frame();
    // TODO: isk needs to be a view of sk as a series of I8.t's
    let isk = create #I8.t #(v crypto_secretkeybytes) crypto_secretkeybytes (I8.int_to_t 0) in

    for 0ul params_n
    (fun h _ -> live h isk /\ live h s)
    (fun i -> isk.(i) <- let sVal = s.(i) in int64_to_int8 sVal);

    // Reference code increments isk by PARAM_N at this point. Originally I tried doing this
    // by redefining isk as a sub of itself, but F* got confused instantiating implicit arguments
    // for fetching entries. Instead, here each reference to isk has params_n added to it.
    for 0ul params_k
    (fun h0 _ -> live h0 isk /\ live h0 e)
    (fun k -> for 0ul params_n
           (fun h1 _ -> live h1 isk /\ live h1 e)
           (fun i -> isk.(params_n +. k *. params_n +. i) <- let eVal = e.(k *. params_n +. i) in
                                                             int64_to_int8 eVal)
    );

    update_sub isk (params_n +. params_k *. params_n) ((size 2) *. crypto_seedbytes) seeds;

    // TODO: try to avoid this copy back into sk. Determine whether or not int8_to_uint8 is a straightforward
    // byte reinterpretation, or if it does something like taking absolute value. We want a straightforward
    // byte reinterpretation -- basically a direct cast from one to the other. OCaml looks like it does what we
    // want, and Kremlin extracts this as a straight cast.
    for 0ul crypto_secretkeybytes
    (fun h _ -> live h isk /\ live h sk)
    (fun i -> sk.(i) <- let iskVal = isk.(i) in int8_to_uint8 iskVal);

    pop_frame()*)

assume val encode_pk:
    pk: buffer uint8
  -> t: poly_k
  -> seedA: buffer uint8 // TODO: probably a fixed length
  -> Stack unit
    (requires fun h -> live h pk /\ live h t /\ live h seedA /\
                    disjoint pk t /\ disjoint pk seedA /\ disjoint t seedA)
    (ensures fun h0 _ h1 -> modifies (loc pk) h0 h1)

assume val decode_pk:
    pk: buffer uint8
  -> seedA: lbuffer uint8 (v crypto_seedbytes)
  -> pk_in: buffer uint8
  -> Stack unit
    (requires fun h -> live h pk /\ live h seedA /\ live h pk_in /\ disjoint pk seedA /\ disjoint pk pk_in /\ disjoint seedA pk_in)
    (ensures fun h0 _ h1 -> modifies (loc pk |+| loc seedA) h0 h1)

assume val encode_sig:
    sm: buffer uint8
  -> c: buffer uint8
  -> z: poly
  -> Stack unit
    (requires fun h -> live h sm /\ live h c /\ live h z /\ disjoint sm c /\ disjoint sm z /\ disjoint c z)
    (ensures fun h0 _ h1 -> modifies (loc sm) h0 h1)

assume val decode_sig:
    c: buffer uint8
  -> z: poly
  -> sm: buffer uint8
  -> Stack unit
    (requires fun h -> live h c /\ live h z /\ live h sm /\ disjoint c z /\ disjoint c sm /\ disjoint z sm)
    (ensures fun h0 _ h1 -> modifies (loc z |+| loc c) h0 h1)

val qtesla_keygen:
    pk: buffer uint8
  -> sk: buffer uint8
  -> Stack unit
    (requires fun h -> live h pk /\ live h sk /\ disjoint pk sk)
    //(ensures fun h0 _ h1 -> modifies (loc_buffer pk) h0 h1 /\ modifies (loc_buffer sk) h0 h1)
    (ensures fun _ _ _ -> True)

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
      (fun h break -> live h e /\ live h randomness_extended /\
                   (not break ==> (check_ES (get h e k) params_Le)) /\
                   (break ==> (not (check_ES (get h e k) params_Le))))
      (fun _ ->
        let nonce0 = nonce.(size 0) in
        nonce.(size 0) <- nonce0 +. 1;
        sample_gauss_poly e.(k) (sub randomness_extended (k * crypto_seedbytes) crypto_randombytes) nonce;
        not (check_ES e.(k) params_Le)));*)

let qtesla_keygen pk sk =
  push_frame();
  let randomness = create crypto_randombytes (u8 0) in
  let randomness_extended = create randomness_extended_size (u8 0) in
  let e:poly_k = create (params_n *. params_k) (to_elem 0) in
  let s:poly = create params_n (to_elem 0) in
  let s_ntt:poly = create params_n (to_elem 0) in
  let a:poly_k = create (params_n *. params_k) (to_elem 0) in
  let t:poly_k = create (params_n *. params_k) (to_elem 0) in
  // TODO: nonce and mask are signed types! Investigate this.
  let nonce = create 1ul 0L in
  let mask = create 1ul (to_elem 0) in
  R.randombytes_ crypto_randombytes randomness;
  SHA3.shake128_hacl crypto_randombytes randomness randomness_extended_size randomness_extended;

  C.Loops.for (size 0) params_k
      (fun h _ -> live h nonce /\ live h e /\ live h randomness_extended)
      (fun k ->
        C.Loops.do_while
          (fun h break -> live h nonce /\ live h e /\ live h randomness_extended)
                       //(break ==> (not (check_ES (get_poly e k) params_Le))))
          (fun _ ->
            let subbuffer = sub randomness_extended (k *. crypto_seedbytes) crypto_randombytes in
            let nonce0 = nonce.(0ul) in
            nonce.(0ul) <- I64.(nonce0 +^ 1L);
            let nonce1:uint64 = nonce.(0ul) in
            let ek:poly = index_poly e k in
            sample_gauss_poly ek subbuffer nonce1;
            // TODO: ek is a buffer, and so we shouldn't have to refetch it with index_poly to operate on its current value, right?
            not (check_ES ek params_Le)
          )
      );
  C.Loops.do_while
      (fun h break -> live h s /\ live h randomness_extended /\ live h nonce)
                   //(break ==> (not (check_ES s params_Ls)))) // TODO: need Ghost/Tot version of check_ES for invariants
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
              mask.(0ul) <- (params_q -^ tki) >>^ 63ul;
              let mask0:elem = mask.(size 0) in
              tk.(i) <- tki -^ (params_q &^ mask0)
           )
        );

  pack_sk sk s e rndsubbuffer;
  encode_pk pk t rndsubbuffer;

  pop_frame()

assume val sample_y:
    y : poly
  -> seed : lbuffer uint8 (v crypto_randombytes)
  -> nonce: I32.t
  -> Stack unit
    (requires fun h -> live h y /\ live h seed /\ disjoint y seed)
    (ensures fun h0 _ h1 -> live h1 y /\ live h1 seed)

assume val hash_vm:
    c_bin : buffer uint8
  -> v : poly_k
  -> hm : buffer uint8
  -> Stack unit
    (requires fun h -> live h c_bin /\ live h v /\ live h hm /\ disjoint c_bin v /\ disjoint c_bin hm /\ disjoint v hm)
    (ensures fun h0 _ h1 -> live h1 c_bin /\ live h1 v /\ live h1 hm /\ modifies (loc c_bin) h0 h1)

assume val encode_c:
    pos_list : lbuffer UI32.t (v params_h)
  -> sign_list : lbuffer I16.t (v params_h)
  -> c_bin : buffer uint8
  -> Stack unit
    (requires fun h -> live h pos_list /\ live h sign_list /\ live h c_bin /\ disjoint pos_list sign_list /\
                    disjoint pos_list c_bin /\ disjoint sign_list c_bin)
    (ensures fun h0 _ h1 -> live h1 pos_list /\ live h1 sign_list /\ live h1 c_bin /\ modifies2 pos_list sign_list h0 h1)

assume val sparse_mul8:
    prod : poly
  -> sk : buffer uint8
  -> pos_list : lbuffer UI32.t (v params_h)
  -> sign_list : lbuffer I16.t (v params_h)
  -> Stack unit
    (requires fun h -> live h prod /\ live h sk /\ live h pos_list /\ live h sign_list /\ disjoint prod sk /\ disjoint prod pos_list /\ disjoint prod sign_list)
    (ensures fun h0 _ h1 -> live h1 prod /\ live h1 sk /\ live h1 pos_list /\ live h1 sign_list /\ modifies1 prod h0 h1)

assume val test_rejection:
    z : poly
  -> Stack bool
    (requires fun h -> live h z)
    (ensures fun h0 _ h1 -> h0 == h1)

assume val test_v:
    v : poly
  -> Stack I32.t
    (requires fun h -> live h v)
    (ensures fun h0 _ h1 -> h0 == h1)

val crypto_sign:
    #smlennat : size_nat
  -> sm : lbuffer uint8 smlennat
  -> smlen : lbuffer size_t 1
  -> m : buffer uint8
  -> mlen : size_t{B.length m = v mlen}
  -> sk : lbuffer uint8 (v crypto_secretkeybytes)
  -> Stack unit
    (requires fun h -> live h sm /\ live h m /\ live h sk /\ disjoint sm m /\ disjoint sm sk /\ disjoint m sk /\ smlennat = (v (bget h smlen 0)))
    (ensures fun h0 _ h1 -> live h1 sm /\ live h1 m /\ live h1 sk /\ modifies2 sm smlen h0 h1)

let crypto_sign #smlennat sm smlen m mlen sk =
    push_frame();

    let c = create crypto_c_bytes (u8 0) in
    let randomness = create crypto_seedbytes (u8 0) in
    let randomness_input_length:size_t = crypto_randombytes +. crypto_seedbytes +. params_hmbytes in
    let randomness_input = create randomness_input_length (u8 0) in
    let pos_list = create params_h (UI32.uint_to_t 0) in
    let sign_list = create params_h (I16.int_to_t 0) in
    let y:poly = create params_n (to_elem 0) in
    let y_ntt:poly = create params_n (to_elem 0) in
    let sc:poly = create params_n (to_elem 0) in
    let z:poly = create params_n (to_elem 0) in
    let v_:poly_k = create (params_n *. params_k) (to_elem 0) in
    let ec:poly_k = create (params_n *. params_k) (to_elem 0) in
    let a:poly_k = create (params_n *. params_k) (to_elem 0) in
    let rsp = create (size 1) (I32.int_to_t 0) in
    let nonce = create (size 1) (I32.int_to_t 0) in

    R.randombytes_ crypto_randombytes (sub randomness_input crypto_randombytes crypto_randombytes);
    update_sub randomness_input (size 0) crypto_seedbytes (sub sk (crypto_secretkeybytes -. crypto_seedbytes) crypto_seedbytes);
    params_hashG m mlen params_hmbytes (sub randomness_input (crypto_randombytes +. crypto_seedbytes) params_hmbytes);
    params_hashG randomness_input randomness_input_length crypto_seedbytes randomness;

    poly_uniform a (sub #_ #_ #(v crypto_randombytes) sk (crypto_secretkeybytes -. (size 2) *. crypto_seedbytes) crypto_randombytes);

    do_while
        (fun h _ -> live h c /\ live h randomness /\ live h randomness_input /\
                     live h pos_list /\ live h sign_list /\ live h y /\ live h y_ntt /\ live h sc /\ live h z /\
                     live h v_ /\ live h ec /\ live h a /\ live h rsp /\ live h nonce /\ live h sm /\ live h m /\ live h sk)
        (fun _ ->
            nonce.(size 0) <- I32.(nonce.(size 0) +^ 1l);
            sample_y y randomness (nonce.(size 0));
            poly_ntt y_ntt y;
            for 0ul params_k
                (fun h _ -> live h c /\ live h randomness /\  live h randomness_input /\
                     live h pos_list /\ live h sign_list /\ live h y /\ live h y_ntt /\ live h sc /\ live h z /\
                     live h v_ /\ live h ec /\ live h a /\ live h rsp /\ live h nonce /\ live h sm /\ live h m /\ live h sk)
                (fun k ->
                    poly_mul (index_poly v_ k) (index_poly a k) y_ntt
                );

            hash_vm c v_ (sub randomness_input (crypto_randombytes +. crypto_seedbytes) params_hmbytes);
            encode_c pos_list sign_list c;
            sparse_mul8 sc sk pos_list sign_list;
            poly_add z y sc;

            if test_rejection z
            then (false)
            else (
                 push_frame();
                 let k = create (size 1) (size 0) in
                 let break = create (size 1) false in
                 while
                 #(fun h -> live h c /\ live h randomness /\  live h randomness_input /\
                     live h pos_list /\ live h sign_list /\ live h y /\ live h y_ntt /\ live h sc /\ live h z /\
                     live h v_ /\ live h ec /\ live h a /\ live h rsp /\ live h nonce /\ live h sm /\ live h m /\ live h sk /\ live h k /\ live h break)
                 #(fun _ h -> live h c /\ live h randomness /\  live h randomness_input /\
                     live h pos_list /\ live h sign_list /\ live h y /\ live h y_ntt /\ live h sc /\ live h z /\
                     live h v_ /\ live h ec /\ live h a /\ live h rsp /\ live h nonce /\ live h sm /\ live h m /\ live h sk /\ live h k /\ live h break)
                 (fun () -> k.(size 0) <. params_k (*&& not break.(size 0)*))
                 (fun _ ->
                     let kVal:size_t = k.(size 0) in
                     let sk_offset:size_t = (params_n *. (kVal +. (size 1))) in
                     let sublen:size_t = crypto_secretkeybytes -. sk_offset in
                     sparse_mul8 (index_poly ec kVal) (sub #_ #_ #(v sublen) sk sk_offset sublen) pos_list sign_list;
                     poly_sub (index_poly v_ kVal) (index_poly v_ kVal) (index_poly ec kVal);
                     rsp.(size 0) <- test_v (index_poly v_ kVal);
                     if (let rspVal = rsp.(size 0) in not (rspVal = 0l))
                     then ( break.(size 0) <- true )
                     else ( k.(size 0) <- UI32.(k.(size 0) +^ 1ul) )
                 );
                 pop_frame();

                 if (let rspVal = rsp.(size 0) in not (rspVal = 0l))
                 then (false)
                 else (
                      for 0ul mlen
                      (fun h _ -> live h c /\ live h randomness /\  live h randomness_input /\
                     live h pos_list /\ live h sign_list /\ live h y /\ live h y_ntt /\ live h sc /\ live h z /\
                     live h v_ /\ live h ec /\ live h a /\ live h rsp /\ live h nonce /\ live h sm /\ live h m /\ live h sk)
                      (fun i ->
                        sm.(crypto_bytes +. i) <- B.index m i );

                      smlen.(size 0) <- crypto_bytes +. mlen;

                      encode_sig sm c z;

                      true
                      )
                )
           );
    pop_frame()



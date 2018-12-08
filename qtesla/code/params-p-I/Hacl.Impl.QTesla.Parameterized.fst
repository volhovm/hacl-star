module Hacl.Impl.QTesla.Parameterized

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

module SHA3 = Hacl.SHA3
module I8 = FStar.Int8
module I16 = FStar.Int16
module I32 = FStar.Int32
module I64 = FStar.Int64
module UI16 = FStar.UInt16
module UI32 = FStar.UInt32
module UI64 = FStar.UInt64
open FStar.Int.Cast

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open C.Loops

open Hacl.Impl.QTesla.Params
open Hacl.Impl.QTesla.Globals

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --admit_smt_queries true"

// TODO: All the pack.c functions (pack_sk, encode_pk, decode_pk, encode_sig, decode_sig) are very tied to their
// parameter sets. Until we have the project set up to do per-parameter set implementations, assume these functions.
val pack_sk:
    sk: lbuffer uint8 crypto_secretkeybytes
  -> s: poly
  -> e: poly_k
  -> seeds: lbuffer uint8 (2 *. crypto_seedbytes)
  -> Stack unit
    (requires fun h -> live h sk /\ live h s /\ live h e /\ live h seeds /\
                    disjoint sk s /\ disjoint sk e /\ disjoint sk seeds /\
                    disjoint s e /\ disjoint s seeds /\ disjoint e seeds)
    (ensures fun h0 _ h1 -> modifies1 sk h0 h1)

let pack_sk sk s e seeds =
    push_frame();
    // TODO: isk needs to be a view of sk as a series of I8.t's
    let isk = create crypto_secretkeybytes 0y in

    for 0ul params_n
    (fun h _ -> live h isk /\ live h s)
    (fun i -> isk.(i) <- let sVal = s.(i) in elem_to_int8 sVal);

    let iskOrig = isk in
    let isk = sub isk params_n (crypto_secretkeybytes -. params_n) in
    for 0ul params_k
    (fun h _ -> live h isk /\ live h e)
    (fun k -> for 0ul params_n
           (fun h _ -> live h isk /\ live h e)
	   (fun i -> let eVal = e.(k *. params_n +. i) in isk.(k *. params_n +. i) <- elem_to_int8 eVal )
    );

    update_sub #MUT #_ #_ isk (params_k *. params_n) (size 2 *. crypto_seedbytes) seeds;

    // In the reference implementation, isk is an alias for sk. We can't do that in F*. Therefore, with
    // some perf cost, we have to do a copy back into sk. We use iskOrig because we need the pointer to the
    // beginning of the whole array, and at this point isk has been advanced by params_n.
    for 0ul crypto_secretkeybytes
    (fun h _ -> live h sk /\ live h isk)
    (fun i -> let iski = iskOrig.(i) in sk.(i) <- int8_to_uint8 iski );

    pop_frame()

val encode_pk:
    pk: lbuffer uint8 crypto_publickeybytes
  -> t: poly_k
  -> seedA: lbuffer uint8 crypto_seedbytes
  -> Stack unit
    (requires fun h -> live h pk /\ live h t /\ live h seedA /\
                    disjoint pk t /\ disjoint pk seedA /\ disjoint t seedA)
    (ensures fun h0 _ h1 -> modifies (loc pk) h0 h1)

let encode_pk pk t seedA =
    push_frame();

    let iBuf = create (size 1) (size 0) in
    let jBuf = create (size 1) (size 0) in
    // In the reference implementation, pt is a uint32_t alias for pk, which we can't do in F*. To make the
    // code below cleaner, we declare pt to be a buffer of elem, and then when we do the necessary copy into
    // pk, we'll cast each entry into a uint32_t and then write it as little-endian bytes into pk.
    let pt = create (crypto_publickeybytes /. size UI32.n) (to_elem 0) in

    while
    #(fun h -> live h t /\ live h iBuf /\ live h jBuf /\ live h pt)
    #(fun _ h -> live h t /\ live h iBuf /\ live h jBuf /\ live h pt)
    (fun _ -> (jBuf.(size 0)) <. params_n *. params_k *. params_q_log /. size 32)
    (fun _ ->
        let i = iBuf.(size 0) in
	let j = jBuf.(size 0) in

        // I can't think of a better way of doing this, because having buffer index ops in-line causes 
        // typechecking errors. So here I declare a whole range of let bindings for the 32 elements of t
	// starting at index j. I'm open to suggestions for a better way of doing this.
	let tj   = t.(j)          in let tj1 = t.(j+.size 1)   in let tj2  = t.(j+.size 2)  in let tj3  = t.(j+.size 3) in
	let tj4  = t.(j+.size 4)  in let tj5 = t.(j+.size 5)   in let tj6  = t.(j+.size 6)  in let tj7  = t.(j+.size 7) in
	let tj8  = t.(j+.size 8)  in let tj9 = t.(j+.size 9)   in let tj10 = t.(j+.size 10) in let tj11 = t.(j+.size 10) in
	let tj12 = t.(j+.size 12) in let tj13 = t.(j+.size 13) in let tj14 = t.(j+.size 14) in let tj15 = t.(j+.size 15) in
	let tj16 = t.(j+.size 16) in let tj17 = t.(j+.size 17) in let tj18 = t.(j+.size 18) in let tj19 = t.(j+.size 19) in
	let tj20 = t.(j+.size 20) in let tj21 = t.(j+.size 21) in let tj22 = t.(j+.size 22) in let tj23 = t.(j+.size 23) in
	let tj24 = t.(j+.size 24) in let tj25 = t.(j+.size 25) in let tj26 = t.(j+.size 26) in let tj27 = t.(j+.size 27) in
	let tj28 = t.(j+.size 28) in let tj29 = t.(j+.size 29) in let tj30 = t.(j+.size 30) in let tj31 = t.(j+.size 31) in

        pt.(i)          <- tj               |^ (tj1  <<^ 29ul); pt.(i+.size 1)  <- (tj1  >>^  3ul)  |^ (tj2  <<^ 26ul);
	pt.(i+.size 2)  <- (tj2  >>^ 6ul)   |^ (tj3  <<^ 23ul); pt.(i+.size 3)  <- (tj3  >>^  9ul)  |^ (tj4  <<^ 20ul);
	pt.(i+.size 4)  <- (tj4  >>^ 12ul)  |^ (tj5  <<^ 17ul); pt.(i+.size 5)  <- (tj5  >>^ 15ul)  |^ (tj6  <<^ 14ul);
	pt.(i+.size 6)  <- (tj6  >>^ 18ul)  |^ (tj7  <<^ 11ul); pt.(i+.size 7)  <- (tj7  >>^ 21ul)  |^ (tj8  <<^ 8ul);
	pt.(i+.size 8)  <- (tj8  >>^ 24ul)  |^ (tj9  <<^ 5ul);  pt.(i+.size 9)  <- (tj9  >>^ 27ul)  |^ (tj10 <<^ 2ul) |^ (tj11 <<^ 31ul);
	pt.(i+.size 10) <- (tj11 >>^ 1ul)   |^ (tj12 <<^ 28ul); pt.(i+.size 11) <- (tj12 >>^  4ul)  |^ (tj13 <<^ 25ul);
	pt.(i+.size 12) <- (tj13 >>^ 7ul)   |^ (tj14 <<^ 22ul); pt.(i+.size 13) <- (tj14 >>^ 10ul)  |^ (tj15 <<^ 19ul);
	pt.(i+.size 14) <- (tj15 >>^ 13ul)  |^ (tj16 <<^ 16ul); pt.(i+.size 15) <- (tj16 >>^ 16ul)  |^ (tj17 <<^ 13ul);
	pt.(i+.size 16) <- (tj17 >>^ 19ul)  |^ (tj18 <<^ 10ul); pt.(i+.size 17) <- (tj18 >>^ 22ul)  |^ (tj19 <<^  7ul);
	pt.(i+.size 18) <- (tj19 >>^ 25ul)  |^ (tj20 <<^  4ul); pt.(i+.size 19) <- (tj20 >>^ 28ul)  |^ (tj21 <<^  1ul) |^ (tj22 <<^ 30ul);
	pt.(i+.size 20) <- (tj22 >>^ 25ul)  |^ (tj23 <<^ 27ul); pt.(i+.size 21) <- (tj23 >>^  5ul)  |^ (tj24 <<^ 24ul);
	pt.(i+.size 22) <- (tj24 >>^ 8ul)   |^ (tj25 <<^ 21ul); pt.(i+.size 23) <- (tj25 >>^ 11ul)  |^ (tj26 <<^ 18ul);
	pt.(i+.size 24) <- (tj26 >>^ 14ul)  |^ (tj27 <<^ 15ul); pt.(i+.size 25) <- (tj27 >>^ 17ul)  |^ (tj28 <<^ 12ul);
	pt.(i+.size 26) <- (tj28 >>^ 20ul)  |^ (tj29 <<^  9ul); pt.(i+.size 27) <- (tj29 >>^ 23ul)  |^ (tj30 <<^  6ul);
	pt.(i+.size 28) <- (tj30 >>^ 26ul)  |^ (tj31 <<^  3ul);
	
        jBuf.(size 0) <- j +. size 32;
	iBuf.(size 0) <- i +. params_q_log
    );

    // Now, we cast each element of pt to a uint32_t, and then write it in four-byte blocks into pk.
    for 0ul (crypto_publickeybytes /. size 4)
    (fun h _ -> live h pk /\ live h pt)
    (fun i -> let pti = pt.(i) in uint_to_bytes_le (sub pk (i *. size 4) (size 4)) (elem_to_uint32 pti));

    update_sub #MUT #_ #_ pk (params_n *. params_k *. params_q_log /. size 8) crypto_seedbytes seedA;
    
    pop_frame()

private
val pt:
    pk : lbuffer uint8 crypto_publickeybytes
  -> j : size_t{j <. crypto_publickeybytes /. size UI32.n}
  -> Stack UI32.t
    (requires fun h -> live h pk)
    (ensures fun h0 _ h1 -> h0 == h1)

let pt pk j =
    uint_from_bytes_le #U32 #PUB (sub pk (j *. size UI32.n) (size UI32.n))

val decode_pk:
    pk : lbuffer I32.t (params_n *. params_k)
  -> seedA : lbuffer uint8 crypto_seedbytes
  -> pk_in : lbuffer uint8 crypto_publickeybytes
  -> Stack unit
    (requires fun h -> live h pk /\ live h seedA /\ live h pk_in)
    (ensures fun h0 _ h1 -> modifies2 pk seedA h0 h1)

let decode_pk pk seedA pk_in =
    push_frame();

    let iBuf = create (size 1) (size 0) in
    let jBuf = create (size 1) (size 0) in
    // In the reference implementation, pp is a uint32_t view into pk. We can't do that in F*, so we operate
    // directly on pk, doing a cast from int32 to uint32 in-line. pt is a uint32_t view into pk, and the
    // function pt above takes care of doing that conversion.
    let mask29:UI32.t = UI32.((1ul <<^ params_q_log) -^ 1ul) in

    while
    #(fun h -> live h pk /\ live h pk_in /\ live h iBuf /\ live h jBuf)
    #(fun _ h -> live h pk /\ live h pk_in /\ live h iBuf /\ live h jBuf)
    (fun _ -> (iBuf.(size 0)) <. (params_n *. params_k))
    (fun _ ->
        let i = iBuf.(size 0) in
	let j = jBuf.(size 0) in

        // Doing these statements in the form of "pk.(i+.size #) <- UI32.(expression)" causes typechecking problems.
	// Lifting the calculation into a let of time UI32.t and then passing it to uint32_to_int32 works at the
	// expense of junking up the code.
        [@inline_let] let u2i = uint32_to_int32 in
        let ppi = UI32.( (pt pk_in j) &^ mask29 ) in  pk.(i) <- u2i ppi;
	let ppi1 = UI32.( (((pt pk_in (j+.size  0)) >>^ 29ul) |^ ((pt pk_in (j+.size  1))) <<^  3ul) &^ mask29 ) in pk.(i+.size 1) <- u2i ppi1;
	let ppi2 = UI32.( (((pt pk_in (j+.size  1)) >>^ 26ul) |^ ((pt pk_in (j+.size  2))) <<^  6ul) &^ mask29 ) in pk.(i+.size 2) <- u2i ppi2;
	let ppi3 = UI32.( (((pt pk_in (j+.size  2)) >>^ 23ul) |^ ((pt pk_in (j+.size  3))) <<^  9ul) &^ mask29 ) in pk.(i+.size  3) <- u2i ppi3;
	let ppi4 = UI32.( (((pt pk_in (j+.size  3)) >>^ 20ul) |^ ((pt pk_in (j+.size  4))) <<^ 12ul) &^ mask29 ) in pk.(i+.size  4) <- u2i ppi4;
	let ppi5 = UI32.( (((pt pk_in (j+.size  4)) >>^ 17ul) |^ ((pt pk_in (j+.size  5))) <<^ 15ul) &^ mask29 ) in pk.(i+.size  5) <- u2i ppi5;
	let ppi6 = UI32.( (((pt pk_in (j+.size  5)) >>^ 14ul) |^ ((pt pk_in (j+.size  6))) <<^ 18ul) &^ mask29 ) in pk.(i+.size  6) <- u2i ppi6;
	let ppi7 = UI32.( (((pt pk_in (j+.size  6)) >>^ 11ul) |^ ((pt pk_in (j+.size  7))) <<^ 21ul) &^ mask29 ) in pk.(i+.size  7) <- u2i ppi7;
	let ppi8 = UI32.( (((pt pk_in (j+.size  7)) >>^  8ul) |^ ((pt pk_in (j+.size  8))) <<^ 24ul) &^ mask29 ) in pk.(i+.size  8) <- u2i ppi8;
	let ppi9 = UI32.( (((pt pk_in (j+.size  8)) >>^  5ul) |^ ((pt pk_in (j+.size  9))) <<^ 27ul) &^ mask29 ) in pk.(i+.size  9) <- u2i ppi9;
	let ppi10 = UI32.(  ((pt pk_in (j+.size  9)) >>^  2ul) &^ mask29 ) in pk.(i+.size 10)  <- u2i ppi10;
	let ppi11 = UI32.( (((pt pk_in (j+.size  9)) >>^ 31ul) |^ ((pt pk_in (j+.size 10))) <<^  1ul) &^  mask29 ) in pk.(i+.size 11) <- u2i ppi11;
	let ppi12 = UI32.( (((pt pk_in (j+.size 10)) >>^ 28ul) |^ ((pt pk_in (j+.size 11))) <<^  4ul) &^ mask29 ) in pk.(i+.size 12) <- u2i ppi12;
	let ppi13 = UI32.( (((pt pk_in (j+.size 11)) >>^ 25ul) |^ ((pt pk_in (j+.size 12))) <<^  7ul) &^ mask29 ) in pk.(i+.size 13) <- u2i ppi13;
	let ppi14 = UI32.( (((pt pk_in (j+.size 12)) >>^ 22ul) |^ ((pt pk_in (j+.size 13))) <<^ 10ul) &^ mask29 ) in pk.(i+.size 14) <- u2i ppi14;
	let ppi15 = UI32.( (((pt pk_in (j+.size 13)) >>^ 19ul) |^ ((pt pk_in (j+.size 14))) <<^ 13ul) &^ mask29 ) in pk.(i+.size 15) <- u2i ppi15;
	let ppi16 = UI32.( (((pt pk_in (j+.size 14)) >>^ 16ul) |^ ((pt pk_in (j+.size 15))) <<^ 16ul) &^ mask29 ) in pk.(i+.size 16) <- u2i ppi16;
	let ppi17 = UI32.( (((pt pk_in (j+.size 15)) >>^ 13ul) |^ ((pt pk_in (j+.size 16))) <<^ 19ul) &^ mask29 ) in pk.(i+.size 17) <- u2i ppi17;
	let ppi18 = UI32.( (((pt pk_in (j+.size 16)) >>^ 10ul) |^ ((pt pk_in (j+.size 17))) <<^ 22ul) &^ mask29 ) in pk.(i+.size 18) <- u2i ppi18;
	let ppi19 = UI32.( (((pt pk_in (j+.size 17)) >>^  7ul) |^ ((pt pk_in (j+.size 18))) <<^ 25ul) &^ mask29 ) in pk.(i+.size 19) <- u2i ppi19;
	let ppi20 = UI32.( (((pt pk_in (j+.size 18)) >>^  4ul) |^ ((pt pk_in (j+.size 19))) <<^ 28ul) &^ mask29 ) in pk.(i+.size 20) <- u2i ppi20;
	let ppi21 = UI32.(  ((pt pk_in (j+.size 19)) >>^  1ul) &^ mask29 ) in pk.(i+.size 21) <- u2i ppi21;
	let ppi22 = UI32.( (((pt pk_in (j+.size 19)) >>^ 30ul) |^ ((pt pk_in (j+.size 20))) <<^  2ul) &^ mask29 ) in pk.(i+.size 22) <- u2i ppi22;
	let ppi23 = UI32.( (((pt pk_in (j+.size 20)) >>^ 27ul) |^ ((pt pk_in (j+.size 21))) <<^  5ul) &^ mask29 ) in pk.(i+.size 23) <- u2i ppi23;
	let ppi24 = UI32.( (((pt pk_in (j+.size 21)) >>^ 24ul) |^ ((pt pk_in (j+.size 22))) <<^  8ul) &^ mask29 ) in pk.(i+.size 24) <- u2i ppi24;
	let ppi25 = UI32.( (((pt pk_in (j+.size 22)) >>^ 21ul) |^ ((pt pk_in (j+.size 23))) <<^ 11ul) &^ mask29 ) in pk.(i+.size 25) <- u2i ppi25;
	let ppi26 = UI32.( (((pt pk_in (j+.size 23)) >>^ 18ul) |^ ((pt pk_in (j+.size 24))) <<^ 14ul) &^ mask29 ) in pk.(i+.size 26) <- u2i ppi26;
	let ppi27 = UI32.( (((pt pk_in (j+.size 24)) >>^ 15ul) |^ ((pt pk_in (j+.size 25))) <<^ 17ul) &^ mask29 ) in pk.(i+.size 27) <- u2i ppi27;
	let ppi28 = UI32.( (((pt pk_in (j+.size 25)) >>^ 12ul) |^ ((pt pk_in (j+.size 26))) <<^ 20ul) &^ mask29 ) in pk.(i+.size 28) <- u2i ppi28;
	let ppi29 = UI32.( (((pt pk_in (j+.size 26)) >>^  9ul) |^ ((pt pk_in (j+.size 27))) <<^ 23ul) &^ mask29 ) in pk.(i+.size 29) <- u2i ppi29;
	let ppi30 = UI32.( (((pt pk_in (j+.size 27)) >>^  6ul) |^ ((pt pk_in (j+.size 28))) <<^ 26ul) &^ mask29 ) in pk.(i+.size 30) <- u2i ppi30;
	let ppi31 = UI32.( (pt pk_in (j+.size 28)) >>^  3ul ) in pk.(i+.size 31) <- u2i ppi31;

        jBuf.(size 0) <- j +. size 29;
	iBuf.(size 0) <- i +. size 32
    );

    copy seedA (sub pk_in (params_n *. params_k *. params_q_log /. size 8) crypto_seedbytes);

    pop_frame()


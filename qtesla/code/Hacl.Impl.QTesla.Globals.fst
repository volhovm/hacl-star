module Hacl.Impl.QTesla.Globals

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open Hacl.Impl.QTesla.Params

module I64 = FStar.Int64

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --admit_smt_queries true"

type poly = lbuffer elem params_n
type poly_k = lbuffer elem (params_k *. params_n)

val poly_create:
    unit
  -> StackInline poly
    (requires fun _ -> True)
    (ensures fun _ _ _ -> True)

let poly_create _ = create params_n (to_elem 0)

val poly_k_create:
    unit
  -> StackInline poly_k
    (requires fun _ -> True)
    (ensures fun _ _ _ -> True)

let poly_k_create _ = create (params_n *. params_k) (to_elem 0)

val get_poly: p: poly_k -> k: size_t{k <. params_k} -> GTot poly
let get_poly p k = gsub p (k *. params_n) params_n

inline_for_extraction
val index_poly: p: poly_k -> k: size_t{k <. params_k} -> Stack poly
    (requires fun h -> live h p)
    (ensures fun h0 pk h1 -> h0 == h1 /\ pk == get_poly p k)
let index_poly p k = sub p (k *. params_n) params_n

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


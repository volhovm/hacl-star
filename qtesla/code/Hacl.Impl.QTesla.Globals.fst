module Hacl.Impl.QTesla.Globals

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open Hacl.Impl.QTesla.Params

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


module Hacl.Impl.QTesla.Params

open FStar.Int
open Lib.IntTypes
open Lib.Buffer
open FStar.Int.Cast

module S = QTesla.Params
module SHA3 = Hacl.SHA3
module I16 = FStar.Int16
module I32 = FStar.Int32
module I64 = FStar.Int64
module UI16 = FStar.UInt16
module UI32 = FStar.UInt32
module UI64 = FStar.UInt64

let crypto_randombytes = size 32
let crypto_seedbytes = size 32
let crypto_c_bytes = size 32

(*
type elem = I32.t
unfold let to_elem = I32.int_to_t
module IElem = FStar.Int32

unfold let elem_to_int16 = int32_to_int16
unfold let int64_to_elem = int64_to_int32
unfold let uint64_to_elem = uint64_to_int32
unfold let elem_to_int64 = int32_to_int64
*)

type elem = I64.t
unfold let to_elem = I64.int_to_t
module IElem = FStar.Int64

unfold let elem_to_int16 = int64_to_int16
unfold let int64_to_elem x = x
unfold let uint64_to_elem = uint64_to_int64
unfold let elem_to_int64 x = x

unfold let op_Plus_Hat = IElem.op_Plus_Hat
unfold let op_Subtraction_Hat = IElem.op_Subtraction_Hat
unfold let op_Star_Hat = IElem.op_Star_Hat
unfold let op_Slash_Hat = IElem.op_Slash_Hat
unfold let op_Percent_Hat = IElem.op_Percent_Hat
unfold let op_Hat_Hat = IElem.op_Hat_Hat
unfold let op_Amp_Hat = IElem.op_Amp_Hat
unfold let op_Bar_Hat = IElem.op_Bar_Hat
unfold let op_Less_Less_Hat = IElem.op_Less_Less_Hat
unfold let op_Greater_Greater_Hat = IElem.op_Greater_Greater_Hat
unfold let op_Equals_Hat = IElem.op_Equals_Hat
unfold let op_Greater_Hat = IElem.op_Greater_Hat
unfold let op_Greater_Equals_Hat = IElem.op_Greater_Equals_Hat
unfold let op_Less_Hat = IElem.op_Less_Hat
unfold let op_Less_Equals_Hat = IElem.op_Less_Equals_Hat

/// Parameters in QTesla.Params aren't marked as unfold or inline_for_extraction;
/// so we need to normalize them here
let params_n = size (normalize_term S.params_n)
let params_k = size (normalize_term S.params_k)
let params_q = to_elem (normalize_term S.params_q)
let params_h = size (normalize_term S.params_h)
let params_Le  = UI32.uint_to_t (normalize_term S.params_Le)
let params_Ls = UI32.uint_to_t (normalize_term S.params_Ls)
let params_d = size (normalize_term S.params_d)
let params_genA = size (normalize_term S.params_bGenA)
let params_barr_mult= I64.int_to_t (normalize_term S.params_barr_mult)
let params_barr_div = UI32.uint_to_t (normalize_term S.params_barr_div)
let params_qinv = I64.int_to_t (normalize_term S.params_qinv)
let params_q_log = size (normalize_term S.params_q_log) // TODO: this can be computed
let params_r2_invn = I64.int_to_t (normalize_term S.params_r2_invn)

// TODO Parameterize.
inline_for_extraction noextract
let params_gaussSampler_xof = SHA3.cshake128_frodo

inline_for_extraction noextract
let params_hashG = SHA3.shake128_hacl

let params_hmbytes = size 64

let crypto_secretkeybytes = normalize_term ((size 2 *. size (I16.n / 8)) *. params_n +. (size 2) *. crypto_seedbytes)
let crypto_bytes = normalize_term (((params_n *. params_d +. size 7) /. (size 8)) +. crypto_c_bytes)

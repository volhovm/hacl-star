// Common types and functions for heuristic parameter sets: I, III-size, III-speed
module Hacl.Impl.QTesla.HeuristicParameters

module I16 = FStar.Int16
module I32 = FStar.Int32
open FStar.Int.Cast
open Lib.IntTypes

type elem = I32.t
unfold let to_elem = I32.int_to_t
module IElem = FStar.Int32
unfold let elem_n = IElem.n

unfold let elem_to_int8 = int32_to_int8
unfold let int8_to_elem = int8_to_int32
unfold let elem_to_uint8 = int32_to_uint8
unfold let uint8_to_elem = uint8_to_int32
unfold let elem_to_int16 = int32_to_int16
unfold let int16_to_elem = int16_to_int32
unfold let elem_to_int32 x = x
unfold let int32_to_elem x = x
unfold let elem_to_uint32 = int32_to_uint32
unfold let uint32_to_elem = uint32_to_int32
unfold let elem_to_int64 = int32_to_int64
unfold let int64_to_elem = int64_to_int32
unfold let elem_to_uint64 = int32_to_uint64
unfold let uint64_to_elem = uint64_to_int32

unfold let sparse_elem = I16.t
unfold let sparse_n = size I16.n
unfold let to_sparse_elem = I16.int_to_t
unfold let sparse_to_int16 x = x

unfold let checkES_t = I32.t
unfold let checkES_n = FStar.UInt32.uint_to_t I32.n
unfold let checkES_init = 0l
unfold let elem_to_checkES_t = elem_to_int32
unfold let checkES_plus = I32.op_Plus_Hat
unfold let checkES_minus = I32.op_Subtraction_Hat
unfold let checkES_sr = I32.op_Greater_Greater_Hat
unfold let checkES_and = I32.op_Amp_Hat
unfold let checkES_or = I32.op_Bar_Hat
unfold let checkES_lognot = I32.lognot
unfold let checkES_to_uint32 = int32_to_uint32

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
unfold let lognot = IElem.lognot


#include "FStar.h"

static uint64_t FStar_UInt128_constant_time_carry(uint64_t a, uint64_t b)
{
  return (a ^ (a ^ b | a - b ^ b)) >> (uint32_t )63;
}

static uint64_t FStar_UInt128_carry(uint64_t a, uint64_t b)
{
  return FStar_UInt128_constant_time_carry(a, b);
}

FStar_UInt128_uint128 FStar_UInt128_add_mod(FStar_UInt128_uint128 a, FStar_UInt128_uint128 b)
{
  return
    (
      (FStar_UInt128_uint128 ){
        .low = a.low + b.low,
        .high = a.high + b.high + FStar_UInt128_carry(a.low + b.low, b.low)
      }
    );
}

FStar_UInt128_uint128 FStar_UInt128_logand(FStar_UInt128_uint128 a, FStar_UInt128_uint128 b)
{
  return ((FStar_UInt128_uint128 ){ .low = a.low & b.low, .high = a.high & b.high });
}

FStar_UInt128_uint128 FStar_UInt128_logor(FStar_UInt128_uint128 a, FStar_UInt128_uint128 b)
{
  return ((FStar_UInt128_uint128 ){ .low = a.low | b.low, .high = a.high | b.high });
}

static uint32_t FStar_UInt128_u32_64 = (uint32_t )64;

static uint64_t FStar_UInt128_add_u64_shift_left(uint64_t hi, uint64_t lo, uint32_t s)
{
  return (hi << s) + (lo >> (FStar_UInt128_u32_64 - s));
}

static uint64_t FStar_UInt128_add_u64_shift_left_respec(uint64_t hi, uint64_t lo, uint32_t s)
{
  return FStar_UInt128_add_u64_shift_left(hi, lo, s);
}

static FStar_UInt128_uint128
FStar_UInt128_shift_left_small(FStar_UInt128_uint128 a, uint32_t s)
{
  if (s == (uint32_t )0)
    return a;
  else
    return
      (
        (FStar_UInt128_uint128 ){
          .low = a.low << s,
          .high = FStar_UInt128_add_u64_shift_left_respec(a.high, a.low, s)
        }
      );
}

static FStar_UInt128_uint128
FStar_UInt128_shift_left_large(FStar_UInt128_uint128 a, uint32_t s)
{
  return
    ((FStar_UInt128_uint128 ){ .low = (uint64_t )0, .high = a.low << (s - FStar_UInt128_u32_64) });
}

FStar_UInt128_uint128 FStar_UInt128_shift_left(FStar_UInt128_uint128 a, uint32_t s)
{
  if (s < FStar_UInt128_u32_64)
    return FStar_UInt128_shift_left_small(a, s);
  else
    return FStar_UInt128_shift_left_large(a, s);
}

static uint64_t FStar_UInt128_add_u64_shift_right(uint64_t hi, uint64_t lo, uint32_t s)
{
  return (lo >> s) + (hi << (FStar_UInt128_u32_64 - s));
}

static uint64_t FStar_UInt128_add_u64_shift_right_respec(uint64_t hi, uint64_t lo, uint32_t s)
{
  return FStar_UInt128_add_u64_shift_right(hi, lo, s);
}

static FStar_UInt128_uint128
FStar_UInt128_shift_right_small(FStar_UInt128_uint128 a, uint32_t s)
{
  if (s == (uint32_t )0)
    return a;
  else
    return
      (
        (FStar_UInt128_uint128 ){
          .low = FStar_UInt128_add_u64_shift_right_respec(a.high, a.low, s),
          .high = a.high >> s
        }
      );
}

static FStar_UInt128_uint128
FStar_UInt128_shift_right_large(FStar_UInt128_uint128 a, uint32_t s)
{
  return
    ((FStar_UInt128_uint128 ){ .low = a.high >> (s - FStar_UInt128_u32_64), .high = (uint64_t )0 });
}

FStar_UInt128_uint128 FStar_UInt128_shift_right(FStar_UInt128_uint128 a, uint32_t s)
{
  if (s < FStar_UInt128_u32_64)
    return FStar_UInt128_shift_right_small(a, s);
  else
    return FStar_UInt128_shift_right_large(a, s);
}

static FStar_UInt128_uint128 FStar_UInt128_uint64_to_uint128(uint64_t a)
{
  return ((FStar_UInt128_uint128 ){ .low = a, .high = (uint64_t )0 });
}

static uint64_t FStar_UInt128_uint128_to_uint64(FStar_UInt128_uint128 a)
{
  return a.low;
}

FStar_UInt128_uint128 FStar_Int_Cast_Full_uint64_to_uint128(uint64_t a)
{
  return FStar_UInt128_uint64_to_uint128(a);
}

uint64_t FStar_Int_Cast_Full_uint128_to_uint64(FStar_UInt128_uint128 a)
{
  return FStar_UInt128_uint128_to_uint64(a);
}


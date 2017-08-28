#include "Poly1305_32.h"

static void Hacl_Bignum_Modulo_reduce(uint32_t *b)
{
  uint32_t b0 = b[0];
  b[0] = (b0 << (uint32_t )2) + b0;
}

static void Hacl_Bignum_Modulo_carry_top(uint32_t *b)
{
  uint32_t b4 = b[4];
  uint32_t b0 = b[0];
  uint32_t b4_26 = b4 >> (uint32_t )26;
  b[4] = b4 & (uint32_t )0x3ffffff;
  b[0] = (b4_26 << (uint32_t )2) + b4_26 + b0;
}

static void Hacl_Bignum_Modulo_carry_top_wide(uint64_t *b)
{
  uint64_t b4 = b[4];
  uint64_t b0 = b[0];
  uint64_t b4_ = b4 & (uint64_t )(uint32_t )0x3ffffff;
  uint32_t b4_26 = (uint32_t )(b4 >> (uint32_t )26);
  uint64_t b0_ = b0 + (uint64_t )((b4_26 << (uint32_t )2) + b4_26);
  b[4] = b4_;
  b[0] = b0_;
}

inline static void Hacl_Bignum_Fproduct_copy_from_wide_(uint32_t *output, uint64_t *input)
{
  {
    uint64_t uu____429 = input[0];
    uint32_t uu____428 = (uint32_t )uu____429;
    output[0] = uu____428;
  }
  {
    uint64_t uu____429 = input[1];
    uint32_t uu____428 = (uint32_t )uu____429;
    output[1] = uu____428;
  }
  {
    uint64_t uu____429 = input[2];
    uint32_t uu____428 = (uint32_t )uu____429;
    output[2] = uu____428;
  }
  {
    uint64_t uu____429 = input[3];
    uint32_t uu____428 = (uint32_t )uu____429;
    output[3] = uu____428;
  }
  {
    uint64_t uu____429 = input[4];
    uint32_t uu____428 = (uint32_t )uu____429;
    output[4] = uu____428;
  }
}

inline static void Hacl_Bignum_Fproduct_shift(uint32_t *output)
{
  uint32_t tmp = output[4];
  {
    uint32_t ctr = (uint32_t )5 - (uint32_t )0 - (uint32_t )1;
    uint32_t z = output[ctr - (uint32_t )1];
    output[ctr] = z;
  }
  {
    uint32_t ctr = (uint32_t )5 - (uint32_t )1 - (uint32_t )1;
    uint32_t z = output[ctr - (uint32_t )1];
    output[ctr] = z;
  }
  {
    uint32_t ctr = (uint32_t )5 - (uint32_t )2 - (uint32_t )1;
    uint32_t z = output[ctr - (uint32_t )1];
    output[ctr] = z;
  }
  {
    uint32_t ctr = (uint32_t )5 - (uint32_t )3 - (uint32_t )1;
    uint32_t z = output[ctr - (uint32_t )1];
    output[ctr] = z;
  }
  output[0] = tmp;
}

inline static void
Hacl_Bignum_Fproduct_sum_scalar_multiplication_(uint64_t *output, uint32_t *input, uint32_t s)
{
  {
    uint64_t uu____871 = output[0];
    uint32_t uu____874 = input[0];
    uint64_t uu____870 = uu____871 + (uint64_t )uu____874 * (uint64_t )s;
    output[0] = uu____870;
  }
  {
    uint64_t uu____871 = output[1];
    uint32_t uu____874 = input[1];
    uint64_t uu____870 = uu____871 + (uint64_t )uu____874 * (uint64_t )s;
    output[1] = uu____870;
  }
  {
    uint64_t uu____871 = output[2];
    uint32_t uu____874 = input[2];
    uint64_t uu____870 = uu____871 + (uint64_t )uu____874 * (uint64_t )s;
    output[2] = uu____870;
  }
  {
    uint64_t uu____871 = output[3];
    uint32_t uu____874 = input[3];
    uint64_t uu____870 = uu____871 + (uint64_t )uu____874 * (uint64_t )s;
    output[3] = uu____870;
  }
  {
    uint64_t uu____871 = output[4];
    uint32_t uu____874 = input[4];
    uint64_t uu____870 = uu____871 + (uint64_t )uu____874 * (uint64_t )s;
    output[4] = uu____870;
  }
}

inline static void Hacl_Bignum_Fproduct_carry_wide_(uint64_t *tmp)
{
  {
    uint32_t ctr = (uint32_t )0;
    uint64_t tctr = tmp[ctr];
    uint64_t tctrp1 = tmp[ctr + (uint32_t )1];
    uint32_t r0 = (uint32_t )tctr & (((uint32_t )1 << (uint32_t )26) - (uint32_t )1);
    uint64_t c = tctr >> (uint32_t )26;
    tmp[ctr] = (uint64_t )r0;
    tmp[ctr + (uint32_t )1] = tctrp1 + c;
  }
  {
    uint32_t ctr = (uint32_t )1;
    uint64_t tctr = tmp[ctr];
    uint64_t tctrp1 = tmp[ctr + (uint32_t )1];
    uint32_t r0 = (uint32_t )tctr & (((uint32_t )1 << (uint32_t )26) - (uint32_t )1);
    uint64_t c = tctr >> (uint32_t )26;
    tmp[ctr] = (uint64_t )r0;
    tmp[ctr + (uint32_t )1] = tctrp1 + c;
  }
  {
    uint32_t ctr = (uint32_t )2;
    uint64_t tctr = tmp[ctr];
    uint64_t tctrp1 = tmp[ctr + (uint32_t )1];
    uint32_t r0 = (uint32_t )tctr & (((uint32_t )1 << (uint32_t )26) - (uint32_t )1);
    uint64_t c = tctr >> (uint32_t )26;
    tmp[ctr] = (uint64_t )r0;
    tmp[ctr + (uint32_t )1] = tctrp1 + c;
  }
  {
    uint32_t ctr = (uint32_t )3;
    uint64_t tctr = tmp[ctr];
    uint64_t tctrp1 = tmp[ctr + (uint32_t )1];
    uint32_t r0 = (uint32_t )tctr & (((uint32_t )1 << (uint32_t )26) - (uint32_t )1);
    uint64_t c = tctr >> (uint32_t )26;
    tmp[ctr] = (uint64_t )r0;
    tmp[ctr + (uint32_t )1] = tctrp1 + c;
  }
}

inline static void Hacl_Bignum_Fproduct_carry_limb_(uint32_t *tmp)
{
  {
    uint32_t ctr = (uint32_t )0;
    uint32_t tctr = tmp[ctr];
    uint32_t tctrp1 = tmp[ctr + (uint32_t )1];
    uint32_t r0 = tctr & (((uint32_t )1 << (uint32_t )26) - (uint32_t )1);
    uint32_t c = tctr >> (uint32_t )26;
    tmp[ctr] = r0;
    tmp[ctr + (uint32_t )1] = tctrp1 + c;
  }
  {
    uint32_t ctr = (uint32_t )1;
    uint32_t tctr = tmp[ctr];
    uint32_t tctrp1 = tmp[ctr + (uint32_t )1];
    uint32_t r0 = tctr & (((uint32_t )1 << (uint32_t )26) - (uint32_t )1);
    uint32_t c = tctr >> (uint32_t )26;
    tmp[ctr] = r0;
    tmp[ctr + (uint32_t )1] = tctrp1 + c;
  }
  {
    uint32_t ctr = (uint32_t )2;
    uint32_t tctr = tmp[ctr];
    uint32_t tctrp1 = tmp[ctr + (uint32_t )1];
    uint32_t r0 = tctr & (((uint32_t )1 << (uint32_t )26) - (uint32_t )1);
    uint32_t c = tctr >> (uint32_t )26;
    tmp[ctr] = r0;
    tmp[ctr + (uint32_t )1] = tctrp1 + c;
  }
  {
    uint32_t ctr = (uint32_t )3;
    uint32_t tctr = tmp[ctr];
    uint32_t tctrp1 = tmp[ctr + (uint32_t )1];
    uint32_t r0 = tctr & (((uint32_t )1 << (uint32_t )26) - (uint32_t )1);
    uint32_t c = tctr >> (uint32_t )26;
    tmp[ctr] = r0;
    tmp[ctr + (uint32_t )1] = tctrp1 + c;
  }
}

inline static void Hacl_Bignum_Fmul_shift_reduce(uint32_t *output)
{
  Hacl_Bignum_Fproduct_shift(output);
  Hacl_Bignum_Modulo_reduce(output);
}

static void
Hacl_Bignum_Fmul_mul_shift_reduce_(uint64_t *output, uint32_t *input, uint32_t *input2)
{
  {
    uint32_t ctr = (uint32_t )5 - (uint32_t )0 - (uint32_t )1;
    uint32_t i1 = ctr;
    uint32_t j = (uint32_t )4 - i1;
    uint32_t input2i = input2[j];
    Hacl_Bignum_Fproduct_sum_scalar_multiplication_(output, input, input2i);
    if (ctr > (uint32_t )0)
      Hacl_Bignum_Fmul_shift_reduce(input);
  }
  {
    uint32_t ctr = (uint32_t )5 - (uint32_t )1 - (uint32_t )1;
    uint32_t i1 = ctr;
    uint32_t j = (uint32_t )4 - i1;
    uint32_t input2i = input2[j];
    Hacl_Bignum_Fproduct_sum_scalar_multiplication_(output, input, input2i);
    if (ctr > (uint32_t )0)
      Hacl_Bignum_Fmul_shift_reduce(input);
  }
  {
    uint32_t ctr = (uint32_t )5 - (uint32_t )2 - (uint32_t )1;
    uint32_t i1 = ctr;
    uint32_t j = (uint32_t )4 - i1;
    uint32_t input2i = input2[j];
    Hacl_Bignum_Fproduct_sum_scalar_multiplication_(output, input, input2i);
    if (ctr > (uint32_t )0)
      Hacl_Bignum_Fmul_shift_reduce(input);
  }
  {
    uint32_t ctr = (uint32_t )5 - (uint32_t )3 - (uint32_t )1;
    uint32_t i1 = ctr;
    uint32_t j = (uint32_t )4 - i1;
    uint32_t input2i = input2[j];
    Hacl_Bignum_Fproduct_sum_scalar_multiplication_(output, input, input2i);
    if (ctr > (uint32_t )0)
      Hacl_Bignum_Fmul_shift_reduce(input);
  }
  {
    uint32_t ctr = (uint32_t )5 - (uint32_t )4 - (uint32_t )1;
    uint32_t i1 = ctr;
    uint32_t j = (uint32_t )4 - i1;
    uint32_t input2i = input2[j];
    Hacl_Bignum_Fproduct_sum_scalar_multiplication_(output, input, input2i);
    if (ctr > (uint32_t )0)
      Hacl_Bignum_Fmul_shift_reduce(input);
  }
}

inline static void Hacl_Bignum_Fmul_fmul_(uint32_t *output, uint32_t *input, uint32_t *input2)
{
  uint64_t t[5] = { 0 };
  Hacl_Bignum_Fmul_mul_shift_reduce_(t, input, input2);
  Hacl_Bignum_Fproduct_carry_wide_(t);
  Hacl_Bignum_Modulo_carry_top_wide(t);
  Hacl_Bignum_Fproduct_copy_from_wide_(output, t);
  uint32_t i0 = output[0];
  uint32_t i1 = output[1];
  uint32_t i0_ = i0 & (((uint32_t )1 << (uint32_t )26) - (uint32_t )1);
  uint32_t i1_ = i1 + (i0 >> (uint32_t )26);
  output[0] = i0_;
  output[1] = i1_;
}

inline static void Hacl_Bignum_Fmul_fmul(uint32_t *output, uint32_t *input, uint32_t *input2)
{
  uint32_t tmp[5] = { 0 };
  memcpy(tmp, input, (uint32_t )5 * sizeof input[0]);
  Hacl_Bignum_Fmul_fmul_(output, tmp, input2);
}

static void
Hacl_Bignum_AddAndMultiply_add_and_multiply(uint32_t *acc, uint32_t *block, uint32_t *r)
{
  {
    uint32_t uu____871 = acc[0];
    uint32_t uu____874 = block[0];
    uint32_t uu____870 = uu____871 + uu____874;
    acc[0] = uu____870;
  }
  {
    uint32_t uu____871 = acc[1];
    uint32_t uu____874 = block[1];
    uint32_t uu____870 = uu____871 + uu____874;
    acc[1] = uu____870;
  }
  {
    uint32_t uu____871 = acc[2];
    uint32_t uu____874 = block[2];
    uint32_t uu____870 = uu____871 + uu____874;
    acc[2] = uu____870;
  }
  {
    uint32_t uu____871 = acc[3];
    uint32_t uu____874 = block[3];
    uint32_t uu____870 = uu____871 + uu____874;
    acc[3] = uu____870;
  }
  {
    uint32_t uu____871 = acc[4];
    uint32_t uu____874 = block[4];
    uint32_t uu____870 = uu____871 + uu____874;
    acc[4] = uu____870;
  }
  Hacl_Bignum_Fmul_fmul(acc, acc, r);
}

inline static void
Hacl_Impl_Poly1305_32_poly1305_update(
  Hacl_Impl_Poly1305_32_State_poly1305_state *st,
  uint8_t *m
)
{
  Hacl_Impl_Poly1305_32_State_poly1305_state scrut0 = st[0];
  uint32_t *h = scrut0.h;
  uint32_t *acc = h;
  Hacl_Impl_Poly1305_32_State_poly1305_state scrut = st[0];
  uint32_t *r = scrut.r;
  uint32_t *r5 = r;
  uint32_t tmp[5] = { 0 };
  uint8_t *s0 = m;
  uint8_t *s1 = m + (uint32_t )3;
  uint8_t *s2 = m + (uint32_t )6;
  uint8_t *s3 = m + (uint32_t )9;
  uint8_t *s4 = m + (uint32_t )12;
  uint32_t i0 = load32_le(s0);
  uint32_t i1 = load32_le(s1);
  uint32_t i2 = load32_le(s2);
  uint32_t i3 = load32_le(s3);
  uint32_t i4 = load32_le(s4);
  uint32_t r0 = i0 & (uint32_t )0x3ffffff;
  uint32_t r1 = i1 >> (uint32_t )2 & (uint32_t )0x3ffffff;
  uint32_t r2 = i2 >> (uint32_t )4 & (uint32_t )0x3ffffff;
  uint32_t r3 = i3 >> (uint32_t )6 & (uint32_t )0x3ffffff;
  uint32_t r4 = i4 >> (uint32_t )8;
  tmp[0] = r0;
  tmp[1] = r1;
  tmp[2] = r2;
  tmp[3] = r3;
  tmp[4] = r4;
  uint32_t b4 = tmp[4];
  uint32_t b4_ = (uint32_t )0x1000000 | b4;
  tmp[4] = b4_;
  Hacl_Bignum_AddAndMultiply_add_and_multiply(acc, tmp, r5);
}

inline static void
Hacl_Impl_Poly1305_32_poly1305_process_last_block_(
  uint8_t *block,
  Hacl_Impl_Poly1305_32_State_poly1305_state *st,
  uint8_t *m,
  uint64_t rem_
)
{
  uint32_t tmp[5] = { 0 };
  uint8_t *s0 = block;
  uint8_t *s1 = block + (uint32_t )3;
  uint8_t *s2 = block + (uint32_t )6;
  uint8_t *s3 = block + (uint32_t )9;
  uint8_t *s4 = block + (uint32_t )12;
  uint32_t i0 = load32_le(s0);
  uint32_t i1 = load32_le(s1);
  uint32_t i2 = load32_le(s2);
  uint32_t i3 = load32_le(s3);
  uint32_t i4 = load32_le(s4);
  uint32_t r0 = i0 & (uint32_t )0x3ffffff;
  uint32_t r1 = i1 >> (uint32_t )2 & (uint32_t )0x3ffffff;
  uint32_t r2 = i2 >> (uint32_t )4 & (uint32_t )0x3ffffff;
  uint32_t r3 = i3 >> (uint32_t )6 & (uint32_t )0x3ffffff;
  uint32_t r4 = i4 >> (uint32_t )8;
  tmp[0] = r0;
  tmp[1] = r1;
  tmp[2] = r2;
  tmp[3] = r3;
  tmp[4] = r4;
  Hacl_Impl_Poly1305_32_State_poly1305_state scrut0 = st[0];
  uint32_t *h = scrut0.h;
  Hacl_Impl_Poly1305_32_State_poly1305_state scrut = st[0];
  uint32_t *r = scrut.r;
  Hacl_Bignum_AddAndMultiply_add_and_multiply(h, tmp, r);
}

inline static void
Hacl_Impl_Poly1305_32_poly1305_process_last_block(
  Hacl_Impl_Poly1305_32_State_poly1305_state *st,
  uint8_t *m,
  uint64_t rem_
)
{
  uint8_t zero1 = (uint8_t )0;
  KRML_CHECK_SIZE(zero1, (uint32_t )16);
  uint8_t block[16];
  for (uintmax_t _i = 0; _i < (uint32_t )16; ++_i)
    block[_i] = zero1;
  uint32_t i0 = (uint32_t )rem_;
  uint32_t i = (uint32_t )rem_;
  memcpy(block, m, i * sizeof m[0]);
  block[i0] = (uint8_t )1;
  Hacl_Impl_Poly1305_32_poly1305_process_last_block_(block, &st[0], m, rem_);
}

static void Hacl_Impl_Poly1305_32_poly1305_last_pass(uint32_t *acc)
{
  Hacl_Bignum_Fproduct_carry_limb_(acc);
  Hacl_Bignum_Modulo_carry_top(acc);
  uint32_t t0 = acc[0];
  uint32_t t10 = acc[1];
  uint32_t t20 = acc[2];
  uint32_t t30 = acc[3];
  uint32_t t40 = acc[4];
  uint32_t t1_ = t10 + (t0 >> (uint32_t )26);
  uint32_t mask_261 = (uint32_t )0x3ffffff;
  uint32_t t0_ = t0 & mask_261;
  uint32_t t2_ = t20 + (t1_ >> (uint32_t )26);
  uint32_t t1__ = t1_ & mask_261;
  uint32_t t3_ = t30 + (t2_ >> (uint32_t )26);
  uint32_t t2__ = t2_ & mask_261;
  uint32_t t4_ = t40 + (t3_ >> (uint32_t )26);
  uint32_t t3__ = t3_ & mask_261;
  acc[0] = t0_;
  acc[1] = t1__;
  acc[2] = t2__;
  acc[3] = t3__;
  acc[4] = t4_;
  Hacl_Bignum_Modulo_carry_top(acc);
  uint32_t t00 = acc[0];
  uint32_t t1 = acc[1];
  uint32_t t2 = acc[2];
  uint32_t t3 = acc[3];
  uint32_t t4 = acc[4];
  uint32_t t1_0 = t1 + (t00 >> (uint32_t )26);
  uint32_t t0_0 = t00 & (uint32_t )0x3ffffff;
  uint32_t t2_0 = t2 + (t1_0 >> (uint32_t )26);
  uint32_t t1__0 = t1_0 & (uint32_t )0x3ffffff;
  uint32_t t3_0 = t3 + (t2_0 >> (uint32_t )26);
  uint32_t t2__0 = t2_0 & (uint32_t )0x3ffffff;
  uint32_t t4_0 = t4 + (t3_0 >> (uint32_t )26);
  uint32_t t3__0 = t3_0 & (uint32_t )0x3ffffff;
  acc[0] = t0_0;
  acc[1] = t1__0;
  acc[2] = t2__0;
  acc[3] = t3__0;
  acc[4] = t4_0;
  Hacl_Bignum_Modulo_carry_top(acc);
  uint32_t i0 = acc[0];
  uint32_t i1 = acc[1];
  uint32_t i0_ = i0 & (((uint32_t )1 << (uint32_t )26) - (uint32_t )1);
  uint32_t i1_ = i1 + (i0 >> (uint32_t )26);
  acc[0] = i0_;
  acc[1] = i1_;
  uint32_t a0 = acc[0];
  uint32_t a1 = acc[1];
  uint32_t a2 = acc[2];
  uint32_t a3 = acc[3];
  uint32_t a4 = acc[4];
  uint32_t mask0 = FStar_UInt32_gte_mask(a0, (uint32_t )0x3fffffb);
  uint32_t mask1 = FStar_UInt32_eq_mask(a1, (uint32_t )0x3ffffff);
  uint32_t mask2 = FStar_UInt32_eq_mask(a2, (uint32_t )0x3ffffff);
  uint32_t mask3 = FStar_UInt32_eq_mask(a3, (uint32_t )0x3ffffff);
  uint32_t mask4 = FStar_UInt32_eq_mask(a4, (uint32_t )0x3ffffff);
  uint32_t mask = mask0 & mask1 & mask2 & mask3 & mask4;
  uint32_t a0_ = a0 - ((uint32_t )0x3fffffb & mask);
  uint32_t a1_ = a1 - ((uint32_t )0x3ffffff & mask);
  uint32_t a2_ = a2 - ((uint32_t )0x3ffffff & mask);
  uint32_t a3_ = a3 - ((uint32_t )0x3ffffff & mask);
  uint32_t a4_ = a4 - ((uint32_t )0x3ffffff & mask);
  acc[0] = a0_;
  acc[1] = a1_;
  acc[2] = a2_;
  acc[3] = a3_;
  acc[4] = a4_;
}

static void
Hacl_Impl_Poly1305_32_mk_state(
  uint32_t *r,
  uint32_t *h,
  Hacl_Impl_Poly1305_32_State_poly1305_state *ret
)
{
  ret[0] = ((Hacl_Impl_Poly1305_32_State_poly1305_state ){ .r = r, .h = h });
}

static void
Hacl_Standalone_Poly1305_32_poly1305_blocks(
  Hacl_Impl_Poly1305_32_State_poly1305_state *st,
  uint8_t *m,
  uint64_t len1
)
{
  if (len1 == (uint64_t )0)
  {
    
  }
  else
  {
    uint8_t *block = m;
    uint8_t *tail1 = m + (uint32_t )16;
    Hacl_Impl_Poly1305_32_poly1305_update(&st[0], block);
    uint64_t len2 = len1 - (uint64_t )1;
    Hacl_Standalone_Poly1305_32_poly1305_blocks(&st[0], tail1, len2);
  }
}

static void
Hacl_Standalone_Poly1305_32_poly1305_partial(
  Hacl_Impl_Poly1305_32_State_poly1305_state *st,
  uint8_t *input,
  uint64_t len1,
  uint8_t *kr
)
{
  Hacl_Impl_Poly1305_32_State_poly1305_state scrut = st[0];
  uint32_t *r = scrut.r;
  uint32_t *x0 = r;
  FStar_UInt128_uint128 k1;
  load128_le(kr, &k1);
  FStar_UInt128_uint128 k_clamped;
  FStar_UInt128_uint128 ret0;
  FStar_UInt128_uint128 ret1;
  FStar_Int_Cast_Full_uint64_to_uint128((uint64_t )0x0ffffffc0fffffff, &ret1);
  FStar_UInt128_uint128 s1 = ret1;
  FStar_UInt128_uint128 ret2;
  FStar_UInt128_uint128 ret3;
  FStar_Int_Cast_Full_uint64_to_uint128((uint64_t )0x0ffffffc0ffffffc, &ret3);
  FStar_UInt128_uint128 s0 = ret3;
  FStar_UInt128_shift_left(&s0, (uint32_t )64, &ret2);
  FStar_UInt128_uint128 s00 = ret2;
  FStar_UInt128_logor(&s00, &s1, &ret0);
  FStar_UInt128_uint128 s10 = ret0;
  FStar_UInt128_logand(&k1, &s10, &k_clamped);
  uint32_t
  r0 = (uint32_t )FStar_Int_Cast_Full_uint128_to_uint64(&k_clamped) & (uint32_t )0x3ffffff;
  FStar_UInt128_uint128 ret4;
  FStar_UInt128_shift_right(&k_clamped, (uint32_t )26, &ret4);
  FStar_UInt128_uint128 s01 = ret4;
  uint32_t r1 = (uint32_t )FStar_Int_Cast_Full_uint128_to_uint64(&s01) & (uint32_t )0x3ffffff;
  FStar_UInt128_uint128 ret5;
  FStar_UInt128_shift_right(&k_clamped, (uint32_t )52, &ret5);
  FStar_UInt128_uint128 s02 = ret5;
  uint32_t r2 = (uint32_t )FStar_Int_Cast_Full_uint128_to_uint64(&s02) & (uint32_t )0x3ffffff;
  FStar_UInt128_uint128 ret6;
  FStar_UInt128_shift_right(&k_clamped, (uint32_t )78, &ret6);
  FStar_UInt128_uint128 s03 = ret6;
  uint32_t r3 = (uint32_t )FStar_Int_Cast_Full_uint128_to_uint64(&s03) & (uint32_t )0x3ffffff;
  FStar_UInt128_uint128 ret;
  FStar_UInt128_shift_right(&k_clamped, (uint32_t )104, &ret);
  FStar_UInt128_uint128 s04 = ret;
  uint32_t r4 = (uint32_t )FStar_Int_Cast_Full_uint128_to_uint64(&s04) & (uint32_t )0x3ffffff;
  x0[0] = r0;
  x0[1] = r1;
  x0[2] = r2;
  x0[3] = r3;
  x0[4] = r4;
  Hacl_Impl_Poly1305_32_State_poly1305_state scrut0 = st[0];
  uint32_t *h = scrut0.h;
  uint32_t *x00 = h;
  x00[0] = (uint32_t )0;
  x00[1] = (uint32_t )0;
  x00[2] = (uint32_t )0;
  x00[3] = (uint32_t )0;
  x00[4] = (uint32_t )0;
  Hacl_Standalone_Poly1305_32_poly1305_blocks(&st[0], input, len1);
}

static void
Hacl_Standalone_Poly1305_32_poly1305_complete(
  Hacl_Impl_Poly1305_32_State_poly1305_state *st,
  uint8_t *m,
  uint64_t len1,
  uint8_t *k1
)
{
  uint8_t *kr = k1;
  uint64_t len16 = len1 >> (uint32_t )4;
  uint64_t rem16 = len1 & (uint64_t )0xf;
  uint8_t *part_input = m;
  uint8_t *last_block = m + (uint32_t )((uint64_t )16 * len16);
  Hacl_Standalone_Poly1305_32_poly1305_partial(&st[0], part_input, len16, kr);
  if (rem16 == (uint64_t )0)
  {
    
  }
  else
    Hacl_Impl_Poly1305_32_poly1305_process_last_block(&st[0], last_block, rem16);
  Hacl_Impl_Poly1305_32_State_poly1305_state scrut = st[0];
  uint32_t *h = scrut.h;
  uint32_t *acc = h;
  Hacl_Impl_Poly1305_32_poly1305_last_pass(acc);
}

static void
Hacl_Standalone_Poly1305_32_crypto_onetimeauth_(
  uint8_t *output,
  uint8_t *input,
  uint64_t len1,
  uint8_t *k1
)
{
  uint32_t buf[10] = { 0 };
  uint32_t *r = buf;
  uint32_t *h = buf + (uint32_t )5;
  Hacl_Impl_Poly1305_32_State_poly1305_state st;
  Hacl_Impl_Poly1305_32_mk_state(r, h, &st);
  uint8_t *key_s = k1 + (uint32_t )16;
  Hacl_Standalone_Poly1305_32_poly1305_complete(&st, input, len1, k1);
  Hacl_Impl_Poly1305_32_State_poly1305_state scrut = st;
  uint32_t *h5 = scrut.h;
  uint32_t *acc = h5;
  FStar_UInt128_uint128 k_;
  load128_le(key_s, &k_);
  uint32_t h0 = acc[0];
  uint32_t h1 = acc[1];
  uint32_t h2 = acc[2];
  uint32_t h3 = acc[3];
  uint32_t h4 = acc[4];
  FStar_UInt128_uint128 ret0;
  FStar_UInt128_uint128 ret1;
  FStar_UInt128_uint128 ret2;
  FStar_UInt128_uint128 ret3;
  FStar_UInt128_uint128 ret4;
  FStar_Int_Cast_Full_uint64_to_uint128((uint64_t )h0, &ret4);
  FStar_UInt128_uint128 s1 = ret4;
  FStar_UInt128_uint128 ret5;
  FStar_UInt128_uint128 ret6;
  FStar_Int_Cast_Full_uint64_to_uint128((uint64_t )h1, &ret6);
  FStar_UInt128_uint128 s0 = ret6;
  FStar_UInt128_shift_left(&s0, (uint32_t )26, &ret5);
  FStar_UInt128_uint128 s00 = ret5;
  FStar_UInt128_logor(&s00, &s1, &ret3);
  FStar_UInt128_uint128 s10 = ret3;
  FStar_UInt128_uint128 ret7;
  FStar_UInt128_uint128 ret8;
  FStar_Int_Cast_Full_uint64_to_uint128((uint64_t )h2, &ret8);
  FStar_UInt128_uint128 s01 = ret8;
  FStar_UInt128_shift_left(&s01, (uint32_t )52, &ret7);
  FStar_UInt128_uint128 s02 = ret7;
  FStar_UInt128_logor(&s02, &s10, &ret2);
  FStar_UInt128_uint128 s11 = ret2;
  FStar_UInt128_uint128 ret9;
  FStar_UInt128_uint128 ret10;
  FStar_Int_Cast_Full_uint64_to_uint128((uint64_t )h3, &ret10);
  FStar_UInt128_uint128 s03 = ret10;
  FStar_UInt128_shift_left(&s03, (uint32_t )78, &ret9);
  FStar_UInt128_uint128 s04 = ret9;
  FStar_UInt128_logor(&s04, &s11, &ret1);
  FStar_UInt128_uint128 s12 = ret1;
  FStar_UInt128_uint128 ret11;
  FStar_UInt128_uint128 ret;
  FStar_Int_Cast_Full_uint64_to_uint128((uint64_t )h4, &ret);
  FStar_UInt128_uint128 s05 = ret;
  FStar_UInt128_shift_left(&s05, (uint32_t )104, &ret11);
  FStar_UInt128_uint128 s06 = ret11;
  FStar_UInt128_logor(&s06, &s12, &ret0);
  FStar_UInt128_uint128 acc_ = ret0;
  FStar_UInt128_uint128 mac_;
  FStar_UInt128_add_mod(&acc_, &k_, &mac_);
  store128_le(output, &mac_);
}

static void
Hacl_Standalone_Poly1305_32_crypto_onetimeauth(
  uint8_t *output,
  uint8_t *input,
  uint64_t len1,
  uint8_t *k1
)
{
  Hacl_Standalone_Poly1305_32_crypto_onetimeauth_(output, input, len1, k1);
}

void *Poly1305_32_op_String_Access(FStar_Monotonic_HyperStack_mem h, uint8_t *b)
{
  return (void *)(uint8_t )0;
}

void
Poly1305_32_mk_state(
  uint32_t *r,
  uint32_t *acc,
  Hacl_Impl_Poly1305_32_State_poly1305_state *ret
)
{
  Hacl_Impl_Poly1305_32_State_poly1305_state ret0;
  Hacl_Impl_Poly1305_32_mk_state(r, acc, &ret0);
  ret[0] = ret0;
}

void Poly1305_32_init(Hacl_Impl_Poly1305_32_State_poly1305_state *st, uint8_t *k1)
{
  Hacl_Impl_Poly1305_32_State_poly1305_state scrut = st[0];
  uint32_t *r = scrut.r;
  uint32_t *x0 = r;
  FStar_UInt128_uint128 k10;
  load128_le(k1, &k10);
  FStar_UInt128_uint128 k_clamped;
  FStar_UInt128_uint128 ret0;
  FStar_UInt128_uint128 ret1;
  FStar_Int_Cast_Full_uint64_to_uint128((uint64_t )0x0ffffffc0fffffff, &ret1);
  FStar_UInt128_uint128 s1 = ret1;
  FStar_UInt128_uint128 ret2;
  FStar_UInt128_uint128 ret3;
  FStar_Int_Cast_Full_uint64_to_uint128((uint64_t )0x0ffffffc0ffffffc, &ret3);
  FStar_UInt128_uint128 s0 = ret3;
  FStar_UInt128_shift_left(&s0, (uint32_t )64, &ret2);
  FStar_UInt128_uint128 s00 = ret2;
  FStar_UInt128_logor(&s00, &s1, &ret0);
  FStar_UInt128_uint128 s10 = ret0;
  FStar_UInt128_logand(&k10, &s10, &k_clamped);
  uint32_t
  r0 = (uint32_t )FStar_Int_Cast_Full_uint128_to_uint64(&k_clamped) & (uint32_t )0x3ffffff;
  FStar_UInt128_uint128 ret4;
  FStar_UInt128_shift_right(&k_clamped, (uint32_t )26, &ret4);
  FStar_UInt128_uint128 s01 = ret4;
  uint32_t r1 = (uint32_t )FStar_Int_Cast_Full_uint128_to_uint64(&s01) & (uint32_t )0x3ffffff;
  FStar_UInt128_uint128 ret5;
  FStar_UInt128_shift_right(&k_clamped, (uint32_t )52, &ret5);
  FStar_UInt128_uint128 s02 = ret5;
  uint32_t r2 = (uint32_t )FStar_Int_Cast_Full_uint128_to_uint64(&s02) & (uint32_t )0x3ffffff;
  FStar_UInt128_uint128 ret6;
  FStar_UInt128_shift_right(&k_clamped, (uint32_t )78, &ret6);
  FStar_UInt128_uint128 s03 = ret6;
  uint32_t r3 = (uint32_t )FStar_Int_Cast_Full_uint128_to_uint64(&s03) & (uint32_t )0x3ffffff;
  FStar_UInt128_uint128 ret;
  FStar_UInt128_shift_right(&k_clamped, (uint32_t )104, &ret);
  FStar_UInt128_uint128 s04 = ret;
  uint32_t r4 = (uint32_t )FStar_Int_Cast_Full_uint128_to_uint64(&s04) & (uint32_t )0x3ffffff;
  x0[0] = r0;
  x0[1] = r1;
  x0[2] = r2;
  x0[3] = r3;
  x0[4] = r4;
  Hacl_Impl_Poly1305_32_State_poly1305_state scrut0 = st[0];
  uint32_t *h = scrut0.h;
  uint32_t *x00 = h;
  x00[0] = (uint32_t )0;
  x00[1] = (uint32_t )0;
  x00[2] = (uint32_t )0;
  x00[3] = (uint32_t )0;
  x00[4] = (uint32_t )0;
}

void *Poly1305_32_empty_log = (void *)(uint8_t )0;

void Poly1305_32_update_block(Hacl_Impl_Poly1305_32_State_poly1305_state *st, uint8_t *m)
{
  Hacl_Impl_Poly1305_32_poly1305_update(&st[0], m);
}

void
Poly1305_32_update(Hacl_Impl_Poly1305_32_State_poly1305_state *st, uint8_t *m, uint32_t len1)
{
  if (len1 == (uint32_t )0)
  {
    
  }
  else
  {
    uint8_t *block = m;
    uint8_t *m_ = m + (uint32_t )16;
    uint32_t len2 = len1 - (uint32_t )1;
    Poly1305_32_update_block(&st[0], block);
    Poly1305_32_update(&st[0], m_, len2);
  }
}

void
Poly1305_32_update_last(
  Hacl_Impl_Poly1305_32_State_poly1305_state *st,
  uint8_t *m,
  uint32_t len1
)
{
  if ((uint64_t )len1 == (uint64_t )0)
  {
    
  }
  else
    Hacl_Impl_Poly1305_32_poly1305_process_last_block(&st[0], m, (uint64_t )len1);
  Hacl_Impl_Poly1305_32_State_poly1305_state scrut = st[0];
  uint32_t *h = scrut.h;
  uint32_t *acc = h;
  Hacl_Impl_Poly1305_32_poly1305_last_pass(acc);
}

void
Poly1305_32_finish(Hacl_Impl_Poly1305_32_State_poly1305_state *st, uint8_t *mac, uint8_t *k1)
{
  Hacl_Impl_Poly1305_32_State_poly1305_state scrut = st[0];
  uint32_t *h = scrut.h;
  uint32_t *acc = h;
  FStar_UInt128_uint128 k_;
  load128_le(k1, &k_);
  uint32_t h0 = acc[0];
  uint32_t h1 = acc[1];
  uint32_t h2 = acc[2];
  uint32_t h3 = acc[3];
  uint32_t h4 = acc[4];
  FStar_UInt128_uint128 ret0;
  FStar_UInt128_uint128 ret1;
  FStar_UInt128_uint128 ret2;
  FStar_UInt128_uint128 ret3;
  FStar_UInt128_uint128 ret4;
  FStar_Int_Cast_Full_uint64_to_uint128((uint64_t )h0, &ret4);
  FStar_UInt128_uint128 s1 = ret4;
  FStar_UInt128_uint128 ret5;
  FStar_UInt128_uint128 ret6;
  FStar_Int_Cast_Full_uint64_to_uint128((uint64_t )h1, &ret6);
  FStar_UInt128_uint128 s0 = ret6;
  FStar_UInt128_shift_left(&s0, (uint32_t )26, &ret5);
  FStar_UInt128_uint128 s00 = ret5;
  FStar_UInt128_logor(&s00, &s1, &ret3);
  FStar_UInt128_uint128 s10 = ret3;
  FStar_UInt128_uint128 ret7;
  FStar_UInt128_uint128 ret8;
  FStar_Int_Cast_Full_uint64_to_uint128((uint64_t )h2, &ret8);
  FStar_UInt128_uint128 s01 = ret8;
  FStar_UInt128_shift_left(&s01, (uint32_t )52, &ret7);
  FStar_UInt128_uint128 s02 = ret7;
  FStar_UInt128_logor(&s02, &s10, &ret2);
  FStar_UInt128_uint128 s11 = ret2;
  FStar_UInt128_uint128 ret9;
  FStar_UInt128_uint128 ret10;
  FStar_Int_Cast_Full_uint64_to_uint128((uint64_t )h3, &ret10);
  FStar_UInt128_uint128 s03 = ret10;
  FStar_UInt128_shift_left(&s03, (uint32_t )78, &ret9);
  FStar_UInt128_uint128 s04 = ret9;
  FStar_UInt128_logor(&s04, &s11, &ret1);
  FStar_UInt128_uint128 s12 = ret1;
  FStar_UInt128_uint128 ret11;
  FStar_UInt128_uint128 ret;
  FStar_Int_Cast_Full_uint64_to_uint128((uint64_t )h4, &ret);
  FStar_UInt128_uint128 s05 = ret;
  FStar_UInt128_shift_left(&s05, (uint32_t )104, &ret11);
  FStar_UInt128_uint128 s06 = ret11;
  FStar_UInt128_logor(&s06, &s12, &ret0);
  FStar_UInt128_uint128 acc_ = ret0;
  FStar_UInt128_uint128 mac_;
  FStar_UInt128_add_mod(&acc_, &k_, &mac_);
  store128_le(mac, &mac_);
}

void
Poly1305_32_crypto_onetimeauth(uint8_t *output, uint8_t *input, uint64_t len1, uint8_t *k1)
{
  Hacl_Standalone_Poly1305_32_crypto_onetimeauth(output, input, len1, k1);
}


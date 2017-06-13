/* #include "kremlib.h" */

typedef struct {
  uint64_t high;
  uint64_t low;
} UInt115_t;

typedef UInt115_t Hacl_UInt115_t;

static inline UInt115_t Hacl_UInt115__uint64_to_uint115(uint64_t x) {
  UInt115_t r;
  r.low = x & 0x7ffffffffffff;
  r.high = x >> 51;
  return r;
}

static inline uint64_t Hacl_UInt115__uint115_to_uint64(UInt115_t r) {
  return r.low + (r.high << 51);
}

static inline UInt115_t Hacl_UInt115_add_mod(UInt115_t x, UInt115_t y) {
  UInt115_t r;
  r.high = x.high + y.high;
  r.low = x.low + y.low;
  return r;
}

static inline UInt115_t Hacl_UInt115_add(UInt115_t x, UInt115_t y) {
  return Hacl_UInt115_add_mod(x,y);
}

static inline UInt115_t Hacl_UInt115_mul_wide(uint64_t x, uint64_t y) {
  uint64_t x0 = x & 0x03ffffff;
  uint64_t x1 = x >> 26;
  uint64_t y0 = y & 0x03ffffff;
  uint64_t y1 = y >> 26;
  uint64_t l = x0*y0;
  uint64_t m = x0*y1 + y0*x1;
  uint64_t h = x1*y1;
  UInt115_t r;
  r.low = l + ((m & 0x1ffffff) << 26);
  r.high = (h << 1) + (m >> 25);
  return r;
}

static inline UInt115_t Hacl_UInt115_square(uint64_t x) {
  uint64_t x0 = x & 0x03ffffff;
  uint64_t x1 = x >> 26;
  uint64_t l = x0*x0;
  uint64_t m = (x0*x1) << 1;
  uint64_t h = x1*x1;
  UInt115_t r;
  r.low = l + ((m & 0x1ffffff) << 26);
  r.high = (h << 1) + (m >> 25);
  return r;
}

static inline uint64_t Hacl_UInt115_split51_high(UInt115_t s) {
  uint64_t h = s.high + (s.low >> 51);
  return h;
}

static inline uint64_t Hacl_UInt115_split51_low(UInt115_t s) {
  uint64_t l = s.low & 0x7ffffffffffff;
  return l;
}


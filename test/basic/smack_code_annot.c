#include "smack.h"

// @expect verified
// @flag --bit-precise --float

typedef unsigned int u32;
typedef unsigned short u16;
typedef unsigned char u8;

u32 u16_to_u32(u16 x) {
  u32 ret = __VERIFIER_nondet_unsigned_int();
  __SMACK_code("@i := $zext.bv16.bv32(@h);", ret, x);
  return ret;
}

u32 u8_to_u32(u8 x) {
  u32 ret = __VERIFIER_nondet_unsigned_int();
  __SMACK_code("@i := $zext.bv8.bv32(@c);", ret, x);
  return ret;
}

double f16_to_f32(float x) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := ftd(RNE, @f);", ret, x);
  return ret;
}

int main(void) {
  u8 x8 = __VERIFIER_nondet_unsigned_char();
  u8 y8 = __VERIFIER_nondet_unsigned_char();
  u16 x16 = __VERIFIER_nondet_unsigned_short();
  u16 y16 = __VERIFIER_nondet_unsigned_short();
  __VERIFIER_assume(x8 > y8);
  __VERIFIER_assume(x16 > y16);
  assert(u8_to_u32(x8) > u8_to_u32(y8));
  assert(u16_to_u32(x16) > u16_to_u32(y16));
  assert(f16_to_f32(2.0f) == 2.0);
  return 0;
}


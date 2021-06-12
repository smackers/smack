#include "smack.h"
#include <assert.h>

// @expect verified

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
  __SMACK_code("@I := $zext.bv8.bv32(@c);", ret, x);
  return ret;
}

u16 u16_id(u16 x) {
  u16 ret = __VERIFIER_nondet_unsigned_short();
  __SMACK_code("@H := @h;", ret, x);
  return ret;
}

u8 u8_id(u8 x) {
  u8 ret = __VERIFIER_nondet_unsigned_char();
  __SMACK_code("@b := @B;", ret, x);
  return ret;
}

int main(void) {
  u8 x8 = __VERIFIER_nondet_unsigned_char();
  u8 y8 = __VERIFIER_nondet_unsigned_char();
  u16 x16 = __VERIFIER_nondet_unsigned_short();
  u16 y16 = __VERIFIER_nondet_unsigned_short();
  assume(u8_id(x8) > u8_id(y8));
  assume(u16_id(x16) > u16_id(y16));
  assert(u8_to_u32(x8) > u8_to_u32(y8));
  assert(u16_to_u32(x16) > u16_to_u32(y16));
  return 0;
}

#include "smack.h"
#include <assert.h>
#include <stdint.h>

// @expect error

uint16_t bitreverse16(uint16_t x) {
  uint16_t result = 0;
  result |= (x & 0x0001) << 15; // 0->15
  result |= (x & 0x0002) << 13; // 1->14
  result |= (x & 0x0004) << 11; // 2->13
  result |= (x & 0x0008) << 9;  // 3->12
  result |= (x & 0x0010) << 7;  // 4->11
  result |= (x & 0x0020) << 5;  // 5->10
  result |= (x & 0x0040) << 3;  // 6->9
  result |= (x & 0x0080) << 1;  // 7->8
  result |= (x & 0x0100) >> 1;  // 8->7
  result |= (x & 0x0200) >> 3;  // 9->6
  result |= (x & 0x0400) >> 5;  // 10->5
  result |= (x & 0x0800) >> 7;  // 11->4
  result |= (x & 0x1000) >> 9;  // 12->3
  result |= (x & 0x2000) >> 11; // 13->2
  result |= (x & 0x4000) >> 13; // 14->1
  result |= (x & 0x8000) >> 15; // 15->0
  return result;
}

uint32_t bitreverse32(uint32_t x) {
  uint32_t result = 0;
  result |= (x & 0x01) << 31; // 0->31
  result |= (x & 0x02) << 29; // 1->30
  result |= (x & 0x04) << 27; // 2->29
  result |= (x & 0x08) << 25; // 3->28
  result |= (x & 0x10) << 23; // 4->27
  result |= (x & 0x20) << 21; // 5->26
  result |= (x & 0x40) << 19; // 6->25
  result |= (x & 0x80) << 17; // 7->24
  result |= bitreverse16((x >> 8) & 0xFFFF) << 8;
  result |= (x & 0x01000000) >> 17; // 24->7
  result |= (x & 0x02000000) >> 19; // 25->6
  result |= (x & 0x04000000) >> 21; // 26->5
  result |= (x & 0x08000000) >> 23; // 27->4
  result |= (x & 0x10000000) >> 25; // 28->3
  result |= (x & 0x20000000) >> 27; // 29->2
  result |= (x & 0x40000000) >> 29; // 30->1
  result |= (x & 0x80000000) >> 31; // 31->0
  return result;
}

int main(void) {
  uint16_t x = __VERIFIER_nondet_unsigned_short();
  uint32_t y = __VERIFIER_nondet_unsigned_int();
  assert(__builtin_bitreverse16(x) != bitreverse16(x) ||
         __builtin_bitreverse32(y) != bitreverse32(y));
  return 0;
}

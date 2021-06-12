#include "smack.h"
#include <assert.h>
#include <stdint.h>

// @expect error

uint16_t bswap16(uint16_t x) {
  uint16_t result = 0;
  result |= (x & 0x00FF) << 8;
  result |= (x & 0xFF00) >> 8;
  return result;
}

uint32_t bswap32(uint32_t x) {
  uint32_t result = 0;
  result |= (x & 0x000000FF) << 24;
  result |= (x & 0x0000FF00) << 8;
  result |= (x & 0x00FF0000) >> 8;
  result |= (x & 0xFF000000) >> 24;
  return result;
}

uint64_t bswap64(uint64_t x) {
  uint64_t result = 0;
  result |= (x & 0x00000000000000FF) << 56;
  result |= (x & 0x000000000000FF00) << 40;
  result |= (x & 0x0000000000FF0000) << 24;
  result |= (x & 0x00000000FF000000) << 8;
  result |= (x & 0x000000FF00000000) >> 8;
  result |= (x & 0x0000FF0000000000) >> 24;
  result |= (x & 0x00FF000000000000) >> 40;
  result |= (x & 0xFF00000000000000) >> 56;
  return result;
}

int main(void) {
  uint16_t x16 = __VERIFIER_nondet_unsigned_short();
  uint32_t x32 = __VERIFIER_nondet_unsigned_int();
  uint64_t x64 = __VERIFIER_nondet_unsigned_long_long();
  assert(__builtin_bswap16(x16) != bswap16(x16) ||
         __builtin_bswap32(x32) != bswap32(x32) ||
         __builtin_bswap64(x64) != bswap64(x64));
  return 0;
}

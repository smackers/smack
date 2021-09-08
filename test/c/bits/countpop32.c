#include "smack.h"
#include <assert.h>
#include <stdint.h>

// @expect verified

uint32_t ctpop32(uint32_t x) {
  uint32_t result = 0;
  result += x & 1;
  x >>= 1;
  result += x & 1;
  x >>= 1;
  result += x & 1;
  x >>= 1;
  result += x & 1;
  x >>= 1;
  result += x & 1;
  x >>= 1;
  result += x & 1;
  x >>= 1;
  result += x & 1;
  x >>= 1;
  result += x & 1;
  x >>= 1;
  result += x & 1;
  x >>= 1;
  result += x & 1;
  x >>= 1;
  result += x & 1;
  x >>= 1;
  result += x & 1;
  x >>= 1;
  result += x & 1;
  x >>= 1;
  result += x & 1;
  x >>= 1;
  result += x & 1;
  x >>= 1;
  result += x & 1;
  x >>= 1;
  result += x & 1;
  x >>= 1;
  result += x & 1;
  x >>= 1;
  result += x & 1;
  x >>= 1;
  result += x & 1;
  x >>= 1;
  result += x & 1;
  x >>= 1;
  result += x & 1;
  x >>= 1;
  result += x & 1;
  x >>= 1;
  result += x & 1;
  x >>= 1;
  result += x & 1;
  x >>= 1;
  result += x & 1;
  x >>= 1;
  result += x & 1;
  x >>= 1;
  result += x & 1;
  x >>= 1;
  result += x & 1;
  x >>= 1;
  result += x & 1;
  x >>= 1;
  result += x & 1;
  x >>= 1;
  result += x & 1;
  return result;
}

int main(void) {
  uint32_t x = __VERIFIER_nondet_unsigned_int();
  assume(x < 1 << 16);
  assert(__builtin_popcount(x) == ctpop32(x));
  uint32_t y = __VERIFIER_nondet_unsigned_int();
  assume(x >= 1 << 16);
  assert(__builtin_popcount(y) == ctpop32(y));
  return 0;
}

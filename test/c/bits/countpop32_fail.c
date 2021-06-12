#include "smack.h"
#include <assert.h>
#include <stdint.h>

// @expect error

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
  assert(__builtin_popcount(x) != ctpop32(x));
  return 0;
}

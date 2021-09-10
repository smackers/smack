#include "smack.h"
#include <assert.h>
#include <stdint.h>

// @expect error

uint32_t ctlz32(uint32_t x) {
  uint32_t n = 32;
  uint32_t y;

  y = x >> 16;
  if (y != 0) {
    n = n - 16;
    x = y;
  }
  y = x >> 8;
  if (y != 0) {
    n = n - 8;
    x = y;
  }
  y = x >> 4;
  if (y != 0) {
    n = n - 4;
    x = y;
  }
  y = x >> 2;
  if (y != 0) {
    n = n - 2;
    x = y;
  }
  y = x >> 1;
  if (y != 0)
    return n - 2;
  return n - x;
}

uint64_t ctlz64(uint64_t x) {
  uint64_t n = 64;
  uint64_t y;

  y = x >> 32;
  if (y != 0) {
    n = n - 32;
    x = y;
  }
  y = x >> 16;
  if (y != 0) {
    n = n - 16;
    x = y;
  }
  y = x >> 8;
  if (y != 0) {
    n = n - 8;
    x = y;
  }
  y = x >> 4;
  if (y != 0) {
    n = n - 4;
    x = y;
  }
  y = x >> 2;
  if (y != 0) {
    n = n - 2;
    x = y;
  }
  y = x >> 1;
  if (y != 0)
    return n - 2;
  return n - x;
}

int main(void) {
  // It appears clang defaults to setting zero arguments
  // to ctlz as having undefined results. This test
  // should fail if this is true.
  uint32_t x32 = __VERIFIER_nondet_unsigned_int();
  uint64_t x64 = __VERIFIER_nondet_unsigned_long_long();
  assert(__builtin_clz(x32) == ctlz32(x32) ||
         __builtin_clzll(x64) == ctlz64(x64));
  return 0;
}

#include "smack.h"
#include <assert.h>
#include <stdint.h>

// @expect verified

uint32_t cttz32(uint32_t x) {
  uint32_t n = 0; /* number of bits */

  if (!(x & 0x0000FFFF)) {
    n += 16;
    x >>= 16;
  }
  if (!(x & 0x000000FF)) {
    n += 8;
    x >>= 8;
  }
  if (!(x & 0x0000000F)) {
    n += 4;
    x >>= 4;
  }
  if (!(x & 0x00000003)) {
    n += 2;
    x >>= 2;
  }

  n += (x & 1) ^ 1;

  return n;
}

uint64_t cttz64(uint64_t x) {
  uint64_t n = 0; /* number of bits */

  if (!(x & 0x00000000FFFFFFFF)) {
    n += 32;
    x >>= 32;
  }
  if (!(x & 0x000000000000FFFF)) {
    n += 16;
    x >>= 16;
  }
  if (!(x & 0x00000000000000FF)) {
    n += 8;
    x >>= 8;
  }
  if (!(x & 0x000000000000000F)) {
    n += 4;
    x >>= 4;
  }
  if (!(x & 0x0000000000000003)) {
    n += 2;
    x >>= 2;
  }

  n += (x & 1) ^ 1;

  return n;
}

int main(void) {
  uint32_t x32 = __VERIFIER_nondet_unsigned_int();
  assume(x32 != 0);
  uint64_t x64 = __VERIFIER_nondet_unsigned_long_long();
  assume(x64 != 0);
  assert(__builtin_ctz(x32) == cttz32(x32));
  assert(__builtin_ctzll(x64) == cttz64(x64));
  return 0;
}

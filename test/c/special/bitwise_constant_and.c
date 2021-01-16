#include "smack.h"

// @expect verified
// @flag --rewrite-bitwise-ops

int main(void) {
  unsigned char x = __VERIFIER_nondet_unsigned_char();
  // 2**0
  assert((x & 0) == 0);

  // 2**1
  assert((x & 1) == x % 2);
  assert((1 & x) == x % 2);

  assert((x & -2) == x - x % 2);
  assert((-2 & x) == x - x % 2);

  // 2**2
  assert((x & 3) == x % 4);
  assert((3 & x) == x % 4);

  assert((x & -4) == x - x % 4);
  assert((-4 & x) == x - x % 4);

  // 2**3
  assert((x & 7) == x % 8);
  assert((7 & x) == x % 8);

  assert((x & -8) == x - x % 8);
  assert((-8 & x) == x - x % 8);

  // 2**4
  assert((x & 15) == x % 16);
  assert((15 & x) == x % 16);

  assert((x & -16) == x - x % 16);
  assert((-16 & x) == x - x % 16);

  // 2**5
  assert((x & 31) == x % 32);
  assert((31 & x) == x % 32);

  assert((x & -32) == x - x % 32);
  assert((-32 & x) == x - x % 32);

  // 2**6
  assert((x & 63) == x % 64);
  assert((63 & x) == x % 64);

  assert((x & -64) == x - x % 64);
  assert((-64 & x) == x - x % 64);

  // 2**7
  assert((x & 127) == x % 128);
  assert((127 & x) == x % 128);

  assert((x & -128) == x - x % 128);
  assert((-128 & x) == x - x % 128);

  // 2**8
  assert((x & 255) == x);

  return 0;
}

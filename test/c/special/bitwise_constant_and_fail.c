#include "smack.h"

// @expect error
// @flag --rewrite-bitwise-ops

int main(void) {
  unsigned char x = __VERIFIER_nondet_unsigned_char();
  unsigned cond = 0;

  // 2**0
  cond = cond || ((x & 0) != 0);

  // 2**1
  cond = cond || ((x & 1) != x % 2);
  cond = cond || ((1 & x) != x % 2);

  cond = cond || ((x & -2) != x - x % 2);
  cond = cond || ((-2 & x) != x - x % 2);

  // 2**2
  cond = cond || ((x & 3) != x % 4);
  cond = cond || ((3 & x) != x % 4);

  cond = cond || ((x & -4) != x - x % 4);
  cond = cond || ((-4 & x) != x - x % 4);

  // 2**3
  cond = cond || ((x & 7) != x % 8);
  cond = cond || ((7 & x) != x % 8);

  cond = cond || ((x & -8) != x - x % 8);
  cond = cond || ((-8 & x) != x - x % 8);

  // 2**4
  cond = cond || ((x & 15) != x % 16);
  cond = cond || ((15 & x) != x % 16);

  cond = cond || ((x & -16) != x - x % 16);
  cond = cond || ((-16 & x) != x - x % 16);

  // 2**5
  cond = cond || ((x & 31) != x % 32);
  cond = cond || ((31 & x) != x % 32);

  cond = cond || ((x & -32) != x - x % 32);
  cond = cond || ((-32 & x) != x - x % 32);

  // 2**6
  cond = cond || ((x & 63) != x % 64);
  cond = cond || ((63 & x) != x % 64);

  cond = cond || ((x & -64) != x - x % 64);
  cond = cond || ((-64 & x) != x - x % 64);

  // 2**7
  cond = cond || ((x & 127) != x % 128);
  cond = cond || ((127 & x) != x % 128);

  cond = cond || ((x & -128) != x - x % 128);
  cond = cond || ((-128 & x) != x - x % 128);

  // 2**8
  cond = cond || ((x & 255) != x);

  assert(cond);
  return 0;
}

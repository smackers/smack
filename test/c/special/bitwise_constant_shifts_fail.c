#include "smack.h"
#include <assert.h>

// @expect error
// @flag --rewrite-bitwise-ops

int main(void) {
  unsigned char x = __VERIFIER_nondet_unsigned_char();
  int cond = 0;
  { // y = 0
    cond = cond || ((x >> 0) != (x / 1));
    cond = cond || ((x << 0) != (x * 1));
  }
  { // y = 1
    cond = cond || ((x >> 1) != (x / 2));
    cond = cond || ((x << 1) != (x * 2));
  }
  { // y = 3
    cond = cond || ((x >> 3) != (x / 8));
    cond = cond || ((x << 3) != (x * 8));
  }
  { // y = 4
    cond = cond || ((x >> 4) != (x / 16));
    cond = cond || ((x << 4) != (x * 16));
  }
  { // y = 5
    cond = cond || ((x >> 5) != (x / 32));
    cond = cond || ((x << 5) != (x * 32));
  }
  { // y = 6
    cond = cond || ((x >> 6) != (x / 64));
    cond = cond || ((x << 6) != (x * 64));
  }
  { // y = 7
    cond = cond || ((x >> 7) != (x / 128));
    cond = cond || ((x << 7) != (x * 128));
  }
  { // y = 8
    cond = cond || ((x >> 8) != 0);
    // This may not be possible to handle correctly.
    cond = cond || ((x << 8) != x * 128 + x * 128);
  }
  assert(cond);
  return 0;
}

#include "smack.h"
#include <assert.h>

// @expect error

int main(void) {
  unsigned char x = (unsigned char)__VERIFIER_nondet_unsigned_char();
  int cond = 0;
  { // y = 0
    cond = cond || ((x & 0) != (x % (0 + 1)));
    cond = cond || ((0 & x) != (x % (0 + 1)));
  }
  { // y = 1
    cond = cond || ((x & 1) != (x % (1 + 1)));
    cond = cond || ((1 & x) != (x % (1 + 1)));
  }
  { // y = 3
    cond = cond || ((x & 3) != (x % (3 + 1)));
    cond = cond || ((3 & x) != (x % (3 + 1)));
  }
  { // y = 7
    cond = cond || ((x & 7) != (x % (7 + 1)));
    cond = cond || ((7 & x) != (x % (7 + 1)));
  }
  { // y = 15
    cond = cond || ((x & 15) != (x % (15 + 1)));
    cond = cond || ((15 & x) != (x % (15 + 1)));
  }
  { // y = 31
    cond = cond || ((x & 31) != (x % (31 + 1)));
    cond = cond || ((31 & x) != (x % (31 + 1)));
  }
  { // y = 63
    cond = cond || ((x & 63) != (x % (63 + 1)));
    cond = cond || ((63 & x) != (x % (63 + 1)));
  }
  { // y = 127
    cond = cond || ((x & 127) != (x % (127 + 1)));
    cond = cond || ((127 & x) != (x % (127 + 1)));
  }
  { // y = 255
    cond = cond || ((x & 255) != x);
    cond = cond || ((255 & x) != x);
  }
  assert(cond);
  return 0;
}

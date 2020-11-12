#include "smack.h"

// @expect verified

int main(void) {
  unsigned char x = (unsigned char)__VERIFIER_nondet_unsigned_char();
  { // y = 0
    __VERIFIER_assert((x & 0) == (x % (0 + 1)));
    __VERIFIER_assert((0 & x) == (x % (0 + 1)));
  }
  { // y = 1
    __VERIFIER_assert((x & 1) == (x % (1 + 1)));
    __VERIFIER_assert((1 & x) == (x % (1 + 1)));
  }
  { // y = 3
    __VERIFIER_assert((x & 3) == (x % (3 + 1)));
    __VERIFIER_assert((3 & x) == (x % (3 + 1)));
  }
  { // y = 7
    __VERIFIER_assert((x & 7) == (x % (7 + 1)));
    __VERIFIER_assert((7 & x) == (x % (7 + 1)));
  }
  { // y = 15
    __VERIFIER_assert((x & 15) == (x % (15 + 1)));
    __VERIFIER_assert((15 & x) == (x % (15 + 1)));
  }
  { // y = 31
    __VERIFIER_assert((x & 31) == (x % (31 + 1)));
    __VERIFIER_assert((31 & x) == (x % (31 + 1)));
  }
  { // y = 63
    __VERIFIER_assert((x & 63) == (x % (63 + 1)));
    __VERIFIER_assert((63 & x) == (x % (63 + 1)));
  }
  { // y = 127
    __VERIFIER_assert((x & 127) == (x % (127 + 1)));
    __VERIFIER_assert((127 & x) == (x % (127 + 1)));
  }
  { // y = 255
    __VERIFIER_assert((x & 255) == x);
    __VERIFIER_assert((255 & x) == x);
  }
}

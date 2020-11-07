#include "smack.h"

// @expect verified

int main(void) {
  unsigned char x = __VERIFIER_nondet_unsigned_char();
  { // y = 0
    __VERIFIER_assert((x >> 0) == (x/1));
    __VERIFIER_assert((x << 0) == (x*1));
  }
  { // y = 1
    __VERIFIER_assert((x >> 1) == (x/2));
    __VERIFIER_assert((x << 1) == (x*2));
  }
  { // y = 3
    __VERIFIER_assert((x >> 3) == (x/8));
    __VERIFIER_assert((x << 3) == (x*8));
  }
  { // y = 4
    __VERIFIER_assert((x >> 4) == (x/16));
    __VERIFIER_assert((x << 4) == (x*16));
  }
  { // y = 5
    __VERIFIER_assert((x >> 5) == (x/32));
    __VERIFIER_assert((x << 5) == (x*32));
  }
  { // y = 6
    __VERIFIER_assert((x >> 6) == (x/64));
    __VERIFIER_assert((x << 6) == (x*64));
  }
  { // y = 7
    __VERIFIER_assert((x >> 7) == (x/128));
    __VERIFIER_assert((x << 7) == (x*128));
  }
  { // y = 8
    __VERIFIER_assert((x >> 8) == 0);
    // This may not be possible to handle correctly.
    __VERIFIER_assert((x << 8) == x*128 + x*128);
  }
}
    

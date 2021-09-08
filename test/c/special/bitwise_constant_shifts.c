#include "smack.h"
#include <assert.h>

// @expect verified
// @flag --rewrite-bitwise-ops

int main(void) {
  unsigned char x = __VERIFIER_nondet_unsigned_char();
  { // y = 0
    assert((x >> 0) == (x / 1));
    assert((x << 0) == (x * 1));
  }
  { // y = 1
    assert((x >> 1) == (x / 2));
    assert((x << 1) == (x * 2));
  }
  { // y = 3
    assert((x >> 3) == (x / 8));
    assert((x << 3) == (x * 8));
  }
  { // y = 4
    assert((x >> 4) == (x / 16));
    assert((x << 4) == (x * 16));
  }
  { // y = 5
    assert((x >> 5) == (x / 32));
    assert((x << 5) == (x * 32));
  }
  { // y = 6
    assert((x >> 6) == (x / 64));
    assert((x << 6) == (x * 64));
  }
  { // y = 7
    assert((x >> 7) == (x / 128));
    assert((x << 7) == (x * 128));
  }
  { // y = 8
    assert((x >> 8) == 0);
    // This may not be possible to handle correctly.
    assert((x << 8) == x * 128 + x * 128);
  }
  return 0;
}

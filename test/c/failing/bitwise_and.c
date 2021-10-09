#include "smack.h"
#include <assert.h>

// @expect verified

int main(void) {
  unsigned char x = (unsigned char)__VERIFIER_nondet_unsigned_char();
  { // y = 0
    assert((x & 0) == (x % (0 + 1)));
    assert((0 & x) == (x % (0 + 1)));
  }
  { // y = 1
    assert((x & 1) == (x % (1 + 1)));
    assert((1 & x) == (x % (1 + 1)));
  }
  { // y = 3
    assert((x & 3) == (x % (3 + 1)));
    assert((3 & x) == (x % (3 + 1)));
  }
  { // y = 7
    assert((x & 7) == (x % (7 + 1)));
    assert((7 & x) == (x % (7 + 1)));
  }
  { // y = 15
    assert((x & 15) == (x % (15 + 1)));
    assert((15 & x) == (x % (15 + 1)));
  }
  { // y = 31
    assert((x & 31) == (x % (31 + 1)));
    assert((31 & x) == (x % (31 + 1)));
  }
  { // y = 63
    assert((x & 63) == (x % (63 + 1)));
    assert((63 & x) == (x % (63 + 1)));
  }
  { // y = 127
    assert((x & 127) == (x % (127 + 1)));
    assert((127 & x) == (x % (127 + 1)));
  }
  { // y = 255
    assert((x & 255) == x);
    assert((255 & x) == x);
  }
  return 0;
}

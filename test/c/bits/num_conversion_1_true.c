#include "smack.h"
#include <assert.h>

// @flag --loop-limit=11
// @flag --unroll=11
// @expect verified

int main() {
  unsigned char x = __VERIFIER_nondet_unsigned_char();
  unsigned char y;
  unsigned char c;

  x = 37;
  y = 0;
  c = 0;
  while (c < (unsigned char)8) {
    unsigned char i = ((unsigned char)1) << c;
    unsigned char bit = x & i;
    if (bit != (unsigned char)0) {
      y = y + i;
    }
    c = c + ((unsigned char)1);
  }
  assert(x == y);

  return 0;
}

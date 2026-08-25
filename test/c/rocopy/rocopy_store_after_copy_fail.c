#include "smack.h"
#include <string.h>

// @flag --memory-intrinsic-summaries
// @expect error

// read-over-copy: stores into the copied range after the memcpy (failing twin)

int main(void) {
  char s[4], d[4];
  char v0 = __VERIFIER_nondet_char();
  char v1 = __VERIFIER_nondet_char();
  s[0] = v0;
  s[1] = v1;
  s[2] = 3;
  s[3] = 4;
  d[0] = 0;
  d[1] = 0;
  d[2] = 0;
  d[3] = 0;
  memcpy(d, s, 4);
  d[1] = 5;
  d[3] = v0;
  __VERIFIER_assert(d[1] == v1);
  return 0;
}

#include "smack.h"
#include <string.h>

// @flag --memory-intrinsic-summaries
// @expect error

// read-over-copy: two memcpys merged at a join point, then copied again (failing twin)

int main(void) {
  char s1[4], s2[4], d[4];
  char v1 = __VERIFIER_nondet_char();
  char v2 = __VERIFIER_nondet_char();
  s1[0] = v1;
  s1[1] = 1;
  s2[0] = v2;
  s2[1] = 2;
  d[0] = 0;
  d[1] = 0;
  if (__VERIFIER_nondet_int())
    memcpy(d, s1, 2);
  else
    memcpy(d, s2, 2);
  memcpy(s1, d, 2);
  __VERIFIER_assert(s1[0] == v1);
  return 0;
}

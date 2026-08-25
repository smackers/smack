#include "smack.h"
#include <string.h>

// @flag --memory-intrinsic-summaries
// @expect verified

// read-over-copy: the copy result read repeatedly at the same and at different
// indices

int main(void) {
  char s[8], d[8];
  int i;
  char v = __VERIFIER_nondet_char();
  s[0] = v;
  s[1] = 1;
  s[2] = v;
  s[3] = 3;
  s[4] = v;
  s[5] = 5;
  s[6] = v;
  s[7] = 7;
  d[0] = 0;
  d[1] = 0;
  d[2] = 0;
  d[3] = 0;
  d[4] = 0;
  d[5] = 0;
  d[6] = 0;
  d[7] = 0;
  memcpy(d, s, 8);
  int sum1 = d[0] + d[2] + d[4] + d[6];
  int sum2 = d[0] + d[2] + d[4] + d[6];
  int odd = d[1] + d[3] + d[5] + d[7];
  __VERIFIER_assert(sum1 == sum2);
  __VERIFIER_assert(sum1 == 4 * (int)v);
  __VERIFIER_assert(odd == 16);
  __VERIFIER_assert(d[6] == v);
  __VERIFIER_assert(d[6] == d[0]);
  return 0;
}

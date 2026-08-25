#include "smack.h"
#include <string.h>

// @flag --memory-intrinsic-summaries
// @expect error

// read-over-copy: acyclic chain of 4 memcpys between distinct regions (failing twin)

int main(void) {
  char a0[2];
  char a1[2];
  char a2[2];
  char a3[2];
  char a4[2];
  char v = __VERIFIER_nondet_char();
  a0[0] = v;
  a0[1] = 0;
  a1[0] = 0;
  a1[1] = 0;
  a2[0] = 0;
  a2[1] = 0;
  a3[0] = 0;
  a3[1] = 0;
  a4[0] = 0;
  a4[1] = 0;
  memcpy(a1, a0, 2);
  memcpy(a2, a1, 2);
  memcpy(a3, a2, 2);
  memcpy(a4, a3, 2);
  __VERIFIER_assert(a4[0] == 0);
  return 0;
}

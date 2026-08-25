// This file is distributed under the MIT License. See LICENSE for details.
// The phi literal in f reaches one call site that consumes it signed and one
// that consumes it unsigned: the meet is Conflict. Conflict renders signed,
// so the signed consumer sees -1 and 5. (The unsigned consumer then sees -1
// instead of UINT_MAX, which is the same limitation the legacy rendering has;
// a single literal cannot serve both windows under the unbounded encoding.)
// @expect verified
// @flag --sign-analysis
#include "smack.h"

int f(int c) {
  int r;
  if (c)
    r = -1;
  else
    r = 5;
  return r;
}

int main(void) {
  int a = f(__VERIFIER_nondet_int());
  unsigned b = f(__VERIFIER_nondet_int());
  if (b > 100u)
    b = 100u;
  __VERIFIER_assert(a < 6);
  return (int)b;
}

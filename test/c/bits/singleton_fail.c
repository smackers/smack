#include "smack.h"

// @expect error
// @flag --no-byte-access-inference

unsigned long counter;

unsigned long bump(unsigned long n) {
  counter += n;
  return counter;
}

int main(void) {
  unsigned long n = __VERIFIER_nondet_ulong();
  counter = 0;
  assert(bump(n) == n + 1);
  return 0;
}

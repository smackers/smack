// simple.c
#include "smack.h"

int incr(int x) {
  return x + 1;
}

int main(void) {
  int a, b;

  a = b = __VERIFIER_nondet_int();
  a = incr(a);
  assert(a == b + 1);
  return 0;
}


#include "smack.h"
#include <stdio.h>
#include <stdlib.h>

// @expect error

int incr(int x) { return ++x; }

int main(void) {
  int a;

  a = -1;
  a = incr(a);
  assert(a == -1);
  return a;
}

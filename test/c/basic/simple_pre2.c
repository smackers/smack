#include "smack.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

// @expect verified

int incr(int x) { return x + 1; }

int main(void) {
  int a;

  a = 1;
  a = incr(a);
  assert(a == 2);
  return a;
}

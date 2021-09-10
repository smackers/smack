#include "smack.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

// @expect verified

short incr(short x) { return ++x; }

int main(void) {
  short a;

  a = -2;
  a = incr(a);
  assert(a > -2);
  return a;
}

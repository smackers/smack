#include "smack.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

// @expect verified

int returnOne() { return 1; }

int main(void) {
  int a;

  a = -1;
  a = returnOne();
  assert(a == 1);
  return a;
}

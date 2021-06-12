#include "smack.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

// @expect verified

int main(void) {
  int a;
  int b;

  a = 1;
  b = 2;
  a = -1;
  assert(b == 3 || a == -1 || b == 0);
  return a;
}

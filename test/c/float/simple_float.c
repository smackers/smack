#include "smack.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

// @expect verified

int main(void) {
  float a;

  a = 3.0f;
  a = 1.5f;
  assert(a == 1.5f);
  return 0;
}

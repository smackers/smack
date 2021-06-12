#include "smack.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

// @expect error

int main(void) {
  float a;

  a = 3.0f;
  a = 1.5f;
  assert(a == 1.4);
  return 0;
}

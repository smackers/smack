#include "smack.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

// @expect verified
// clang-format off
// @flag --transform-out "sed -e 's/[[:digit:]]* verified, [[:digit:]]* error/1 verified, 0 errors/' -e 's/can fail/no bugs/'"
// clang-format on

int main(void) {
  assert(0);
  return 0;
}

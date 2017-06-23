#include <stdio.h>
#include <stdlib.h>
#include "smack.h"

// @expect verified
// @flag --transform-out "sed -e 's/[[:digit:]]* verified, [[:digit:]]* error/1 verified, 0 errors/' -e 's/can fail/no bugs/'"

int main(void) {
  assert (0);
  return 0;
}

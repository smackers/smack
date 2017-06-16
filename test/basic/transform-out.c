#include <stdio.h>
#include <stdlib.h>
#include "smack.h"

// @expect verified
// @flag --transform-out "sed 's/found an error/found no errors/'"

int main(void) {
  assert (0);
  return 0;
}

#include "smack.h"
#include <stdlib.h>

// @expect error

// see: https://github.com/smackers/smack/issues/554
int main(void) {
  int *a;
  int b = a[0];
  return b;
}

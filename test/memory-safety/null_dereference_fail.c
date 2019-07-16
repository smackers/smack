#include "smack.h"
#include <stdlib.h>

// @expect error

int main(void) {
  int *a;
  int b = a[0];
  return b;
}

#include <stdlib.h>
#include "smack.h"

// @expect error

int main(void) {
  int* a;
  int b = a[0];
  return b;
}


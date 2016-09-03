#include <stdio.h>
#include <stdlib.h>
#include "smack.h"

// @expect error

int main(void) {
  int* a;
  int b = a[0];
  printf("%d\n", b);
  return 0;
}


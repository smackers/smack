#include "smack.h"
#include <stdio.h>
#include <stdlib.h>

// @expect error

int x;
int main(void) {
  int *a = &x;
  int c = a[0];
  free(a);
  return c;
}

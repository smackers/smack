#include "smack.h"
#include <stdio.h>
#include <stdlib.h>

// @expect verified

int x;
int main(void) {
  int *a = &x;
  int *b = malloc(4);
  int c = a[0];
  free(b);
  return c;
}

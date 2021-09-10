#include "smack.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

// @expect verified

#define MAXSIZE 10
#define RESET 0

int main() {
  int *a = (int *)malloc(MAXSIZE * sizeof(int));

  a[5] = 10;

  assert(a[5] == 10);

  free(a);
  return 0;
}

#include "smack.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

// @flag --loop-limit=11
// @flag --unroll=11
// @expect error

#define MAXSIZE 10
#define RESET 0

int main() {
  int i = 0;
  int *a = (int *)malloc(MAXSIZE * sizeof(int));

  for (i = 0; i < MAXSIZE - 1; i++) {
    a[i] = RESET;
  }

  assert(a[5] != RESET || a[9] == RESET);

  free(a);
  return 0;
}

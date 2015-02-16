#include <stdio.h>
#include <stdlib.h>
#include "smack.h"

#define MAXSIZE 10
#define RESET 0

int main() {
  int i = 0;
  int *a = (int*)malloc(MAXSIZE * sizeof(int));

  for (i = 0; i < MAXSIZE; i++) {
    a[i] = RESET;
  }

  assert(a[5] == RESET);

  free(a);
  return 0;
}


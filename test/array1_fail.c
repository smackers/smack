#include <stdio.h>
#include <stdlib.h>
#include "smack.h"

#define MAXSIZE 10
#define RESET 0

int main() {
  int *a = (int*)malloc(MAXSIZE * sizeof(int));

  a[5] = 10;

  assert(a[4] == 10 || a[5] == 0);

  free(a);
  return 0;
}


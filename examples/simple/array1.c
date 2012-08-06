#include <stdio.h>
#include <stdlib.h>
#include "smack.h"

#define MAXSIZE 50
#define RESET 0

int main() {
  int *a = (int*)malloc(MAXSIZE * sizeof(int));

  a[5] = 10;

  __SMACK_assert(a[5] == 10);

  free(a);
  return 0;
}


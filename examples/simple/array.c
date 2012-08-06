#include <stdio.h>
#include <stdlib.h>
#include "smack.h"

#define MAXSIZE 50
#define RESET 0

int main() {
  int *a = (int*)malloc(MAXSIZE * sizeof(int));

  free(a);
  return 0;
}


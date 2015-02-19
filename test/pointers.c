#include <stdio.h>
#include <stdlib.h>
#include "smack.h"

void incr(int *x) {
  (*x)++;
}

int main() {
  int *a = (int*)malloc(sizeof(int));
  int *b = (int*)malloc(sizeof(int));

  *a = *b = 0;

  incr(a);
  incr(b);

  assert(*a == 1);
  assert(*b == 1);

  return 0;
}


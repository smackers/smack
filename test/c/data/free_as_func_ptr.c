#include "smack.h"
#include <stdlib.h>

// @expect verified

void free_me(void (*freefun)(void *)) {
  int *x = (int *)malloc(sizeof(int));
  freefun(x);
}

int main(void) {
  free_me(free);
  return 0;
}

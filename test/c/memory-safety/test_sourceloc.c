#include "smack.h"
#include <stdlib.h>

// @expect verified

int main(void) {
  int *a;
  int ret;

  if (__VERIFIER_nondet_int())
    a = (int *)malloc(sizeof(int));
  else
    a = NULL;

  ret = a ? *a : 0;
  free(a);
  return ret;
}

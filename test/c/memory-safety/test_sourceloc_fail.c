#include "smack.h"
#include <stdlib.h>

// @expect error
// @checkout grep -v "test_sourceloc_fail.c(16,9)"

int main(void) {
  int *a;
  int ret;

  if (__VERIFIER_nondet_int())
    a = (int *)malloc(sizeof(int));
  else
    a = NULL;

  ret = *a;
  free(a);
  return ret;
}

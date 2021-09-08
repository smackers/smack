#include "smack.h"
#include <assert.h>
#include <stdlib.h>

// @expect error

int main(void) {
  int *arr = (int *)calloc(5, sizeof(int));
  int idx = __VERIFIER_nondet_int();
  if (arr == NULL)
    return 1;
  assert(arr[idx] == 0);
  free(arr);
  return 0;
}

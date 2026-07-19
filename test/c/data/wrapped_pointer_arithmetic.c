#include "smack.h"
#include <assert.h>
#include <stdlib.h>

// @expect verified
// @flag --integer-encoding=wrapped-integer

int main() {
  int *arr = (int *)malloc(3 * sizeof(int));
  unsigned long long idx = __VERIFIER_nondet_unsigned_long_long();

  assume(arr[0] < 4);
  assume(arr[1] < 5);
  assume(arr[2] < 6);
  assume(idx < 3);

  assert(arr[idx] <= 5);
  return 0;
}

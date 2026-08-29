#include "smack.h"
#include <assert.h>

// @expect error
// The store and the load are on the same object: the store is region-relevant
// and must be retained, so the error is still reachable.

int main(void) {
  int x = 0;
  int *p = &x;
  int *q = &x;
  *p = 1;
  assert(*q == 0);
  return 0;
}

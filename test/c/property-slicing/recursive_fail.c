#include "smack.h"
#include <assert.h>

// @expect error
// @flag --unroll=4

int down(int n) {
  if (n <= 0)
    return 0;
  return 1 + down(n - 1);
}

int main(void) {
  assert(down(2) != 2);
  return 0;
}

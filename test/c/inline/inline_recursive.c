#include "smack.h"
#include <assert.h>

// @expect verified
// @flag --unroll=5
// @checkbpl grep "call .* := sum("

// A recursive function is left as it is, and so are the calls to it.
int sum(int n) { return n == 0 ? 0 : n + sum(n - 1); }

int main(void) {
  assert(sum(3) == 6);
  return 0;
}

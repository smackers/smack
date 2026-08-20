#include <assert.h>

// @expect verified
// @flag --static-unroll
// @checkbpl grep -q lambda
// @checkout awk '/SMACK warning: found loop/ { found = 1 } END { exit found }'

int main(void) {
  unsigned a[100000];

  for (unsigned i = 0; i < 100000; ++i)
    a[i] = 42;

  assert(a[0] == 42);
  assert(a[99999] == 42);
  return 0;
}

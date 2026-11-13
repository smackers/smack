#include <assert.h>

// @expect verified
// @checkbpl grep -q lambda
// @checkout awk '/SMACK warning: found loop/ { found = 1 } END { exit found }'

int main(void) {
  unsigned a[4096];

  for (unsigned i = 0; i < 4096; ++i)
    a[i] = i;

  assert(a[0] == 0);
  assert(a[2048] == 2048);
  assert(a[4095] == 4095);
  return 0;
}

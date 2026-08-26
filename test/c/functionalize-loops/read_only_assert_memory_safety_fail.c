#include "smack.h"
#include <assert.h>

// @expect error
// @flag --check=memory-safety
// @checkbpl grep -q "assertion loop summary for bad_assert"
// @checkbpl grep -q "functional.read.check"
// @checkout awk '/SMACK warning: found loop/ {x=1} END{exit x}'

static void bad_assert(const unsigned char *a, unsigned n) {
  for (unsigned i = 0; i < n; ++i)
    assert(a[i] == 0);
}

int main(void) {
  unsigned char a[4] = {0};
  bad_assert(a + 4, 1);
  return 0;
}

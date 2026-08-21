#include "smack.h"
#include <assert.h>

// @expect error
// @flag --check=memory-safety --unroll=2
// @checkbpl awk '/summary for bad_assert/{x=1}END{exit x}'
// @checkout grep -F "SMACK warning: found loop"

static void bad_assert(const unsigned char *a, unsigned n) {
  for (unsigned i = 0; i < n; ++i)
    assert(a[i] == 0);
}

int main(void) {
  unsigned char a[4] = {0};
  bad_assert(a + 4, 1);
  return 0;
}

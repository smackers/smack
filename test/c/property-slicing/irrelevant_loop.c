#include "smack.h"
#include <assert.h>

// @expect verified
// The loop needs 1000 iterations but writes only an object the property never
// observes. It must be bypassed rather than unrolled -- the default test
// --unroll=2 would otherwise miss nothing here, but the point is that the
// verdict is unchanged when the loop disappears.

int main(void) {
  int scratch[4];
  int i;
  int watched = 1;
  for (i = 0; i < 1000; i++) {
    scratch[i % 4] = i;
  }
  assert(watched == 1);
  return 0;
}

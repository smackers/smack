#include "smack.h"
#include <assert.h>

// @expect verified
// @flag -x svcomp
// @checkbpl grep -q 'var \$M\.L\.'

static int read_local(int value) {
  int local[2];
  local[0] = value;
  local[1] = value + 1;
  return local[0];
}

int main(void) {
  assert(read_local(42) == 42);
  return 0;
}

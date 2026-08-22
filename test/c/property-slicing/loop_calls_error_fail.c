#include "smack.h"
#include <assert.h>
// @expect error
// @flag --unroll=6

void check(int i) {
  if (i == 2) {
    assert(0);
  }
}

int main(void) {
  int i;
  for (i = 0; i < 4; i++) {
    check(i);
  }
  return 0;
}

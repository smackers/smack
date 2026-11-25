#include "smack.h"
#include <assert.h>
// @expect error
// @flag --unroll=6

int main(void) {
  int x = 0;
  int i;
  for (i = 0; i < 4; i++) {
    x += 1;
  }
  assert(x != 4);
  return 0;
}

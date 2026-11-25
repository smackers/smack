#include "smack.h"
#include <assert.h>
// @expect error
// @flag --unroll=5

int main(void) {
  int x = 0;
  int i, j;
  for (i = 0; i < 3; i++) {
    for (j = 0; j < 3; j++) {
      x++;
    }
  }
  assert(x != 9);
  return 0;
}

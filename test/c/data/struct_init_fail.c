#include "smack.h"
#include <assert.h>

// @expect error

struct a {
  int i;
  int j;
};

int main(void) {
  struct a x = {0, 0};
  assert(x.j == 1);
  return 0;
}

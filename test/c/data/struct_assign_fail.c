#include "smack.h"
#include <assert.h>

// @expect error

struct a {
  int i;
  int j;
};

int main(void) {
  struct a x = {10, 20};
  assert(x.j == 10);
  return 0;
}

#include "smack.h"
#include <assert.h>

// @expect verified

struct a {
  int i;
  int j;
};

int main(void) {
  struct a x = {10, 20};
  char *p = (char *)&x + 1;
  *p = 1;
  assert(x.j == 20);
  return 0;
}

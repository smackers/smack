#include "smack.h"

// @expect verified

struct a {
  int i;
  int j;
};

int main(void) {
  struct a x = {10, 20};
  assert(x.j == 20);
  return 0;
}

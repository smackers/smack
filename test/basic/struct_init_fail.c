#include <smack.h>

// @flag --unroll=2
// @expect error

struct a {
  int i;
  int j;
};

int main(void) {
  struct a x = {0,0};
  assert(x.j == 1);
  return 0;
}


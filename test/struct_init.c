#include <smack.h>

struct a {
  int i;
  int j;
};

int main(void) {
  struct a x = {0,0};
  __SMACK_assert(x.i == 0 && x.j == 0);
  return 0;
}


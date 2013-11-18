#include "smack.h"

struct a {
  int i;
  int j;
};

int main(void) {
  struct a x = {10, 20};
  __SMACK_assert(x.j == 10);
  return 0;
}


#include <stdlib.h>
#include <smack.h>

struct a {
  int i;
  int j;
};

int main() {
  struct a x = {0,0};
  __SMACK_assert(x.i == 0);
}
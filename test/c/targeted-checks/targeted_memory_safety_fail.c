#include "smack.h"
#include <stdlib.h>

// @flag --checked-functions main get_last
// @flag --check memory-safety
// @expect error

struct BUF {
  int *x;
  size_t size;
};

int get_last(struct BUF b) {
  // Access one past end of array
  return b.x[b.size];
}

int main() {
  int a[5] = {};
  struct BUF x = {a, 5};
  return get_last(x);
}

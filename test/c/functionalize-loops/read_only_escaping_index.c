#include "smack.h"

// @expect verified
// @checkbpl awk '/summary for first_nonzero/{x=1}END{exit x}'

static int first_nonzero(const unsigned char *a, unsigned n) {
  for (unsigned i = 0; i < n; ++i)
    if (a[i] != 0)
      return (int)i;
  return -1;
}

int main(void) {
  unsigned char a[4] = {0};
  return first_nonzero(a, 4);
}

// This file is distributed under the MIT License. See LICENSE for details.

// @expect verified
// @checkbpl awk '/var \$Alloc\.[0-9]+:/ {n++} END {exit n != 1}'

#include <stdlib.h>

int *make(void) { return malloc(sizeof(int)); }

void destroy(int *p) {
  *p = 1;
  free(p);
}

int main(void) {
  int *p = make();
  destroy(p);
  return 0;
}

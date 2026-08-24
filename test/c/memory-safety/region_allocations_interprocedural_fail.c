// This file is distributed under the MIT License. See LICENSE for details.

// @expect error
// @checkout grep "SMACK found an error: invalid pointer dereference."
// @checkbpl awk '/var \$Alloc\.[0-9]+:/ {n++} END {exit n != 2}'

#include <stdlib.h>

// The allocation, the free, and the offending dereference each happen in a
// different procedure, so the class selected for the check has to agree with
// the one threaded through the callees.

int *make(void) { return malloc(sizeof(int)); }

void destroy(int *p) {
  *p = 1;
  free(p);
}

int use(int *p) { return *p; }

int main(void) {
  int *p = make();
  int *q = malloc(sizeof(int));

  *q = 2;
  destroy(p);

  int result = use(p);

  free(q);
  return result;
}

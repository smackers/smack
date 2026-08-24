// This file is distributed under the MIT License. See LICENSE for details.

// @expect error
// @checkout grep "SMACK found an error: invalid pointer dereference."
// @checkbpl awk '/var \$Alloc\.[0-9]+:/ {n++} END {exit n != 2}'

#include <stdlib.h>

// Two independent allocation classes, with the dereference checked against the
// class whose liveness bit was cleared. A split that consulted the wrong map
// would report this program as verified.

int main(void) {
  int *a = malloc(sizeof(int));
  int *b = malloc(sizeof(int));

  *a = 1;
  *b = 2;

  free(a);
  int result = *a;

  free(b);
  return result;
}

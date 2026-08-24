// This file is distributed under the MIT License. See LICENSE for details.

// @expect verified
// @checkbpl awk '/var \$Alloc\.[0-9]+:/ {n++} END {exit n != 1}'
// @checkbpl grep "\$Alloc.0 := malloc"

#include <smack.h>
#include <stdlib.h>

int main(void) {
  int *a = malloc(sizeof(int));
  int *b = malloc(sizeof(int));
  int *p = __VERIFIER_nondet_int() ? a : b;

  *p = 1;

  free(a);
  free(b);
  return 0;
}

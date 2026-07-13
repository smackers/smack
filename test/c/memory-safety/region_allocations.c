// This file is distributed under the MIT License. See LICENSE for details.

// @expect verified
// @checkbpl awk '/var \$Alloc\.[0-9]+:/ {n++} END {exit n != 2}'
// @checkbpl grep "\$Alloc.0 := malloc"
// @checkbpl grep "\$Alloc.1 := malloc"

#include <stdlib.h>

int main(void) {
  int *a = malloc(sizeof(int));
  int *b = malloc(sizeof(int));

  *a = 1;
  *b = 2;
  int result = *a + *b;

  free(a);
  free(b);
  return result;
}

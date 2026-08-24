// This file is distributed under the MIT License. See LICENSE for details.

// @expect error
// @checkbpl awk '/var \$Alloc\.[0-9]+:/ {n++} END {exit n != 2}'

#include <stdlib.h>

// Two allocation classes; `a` is freed twice so the second free has to observe
// the liveness bit its own class cleared. `b` is deliberately left unfreed so
// that the allocation counter balances: if the split ever loses the free, this
// program verifies cleanly instead of trading one error message for another.

int main(void) {
  int *a = malloc(sizeof(int));
  int *b = malloc(sizeof(int));

  *a = 1;
  *b = 2;

  free(a);
  free(a);

  return 0;
}

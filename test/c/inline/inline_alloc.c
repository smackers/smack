#include "smack.h"
#include <assert.h>
#include <stdlib.h>

// @expect verified
// @checkbpl awk '/call .*make\(/ {n++} END {exit n != 0}'

// Small enough to be inlined into both callers, after which no call to it is
// left in the program.
int *make(int v) {
  int *p = (int *)malloc(sizeof(int));
  *p = v;
  return p;
}

int main(void) {
  int *a = make(1);
  int *b = make(2);
  assert(*a == 1);
  assert(*b == 2);
  free(a);
  free(b);
  return 0;
}

// This file is distributed under the MIT License. See LICENSE for details.
// @expect error
// @flag --sign-analysis
#include "smack.h"
#include <assert.h>

// Failing twin of sign_analysis_intptr_alias.c: the store through the
// integer-rebuilt pointer must be visible to the direct field access.
struct S {
  int a;
  int b;
} g;

int main(void) {
  unsigned long tmp = (unsigned long)&g + 4;
  int *pb = (int *)tmp;
  g.b = 7;
  *pb = 5;
  assert(g.b == 7);
  return 0;
}

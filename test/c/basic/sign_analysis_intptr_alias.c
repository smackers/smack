// This file is distributed under the MIT License. See LICENSE for details.
// @expect verified
// @flag --sign-analysis
// @checkbpl awk '/(__ubsan|llvm[.]ubsantrap|[.]src: ref)/ { exit 1 }'
#include "smack.h"
#include <assert.h>

// A store through a pointer rebuilt from integer arithmetic on the address
// of a global must land in the same memory region as a direct field access.
// The annotation-only sanitizer cleanup used to constant-fold the
// `inttoptr(add(ptrtoint @g, 4))` chain into a ConstantExpr, which the
// pointer analysis could no longer relate to `g`; the two accesses were then
// modeled by different maps and the assertion below was wrongly refutable.
struct S {
  int a;
  int b;
} g;

int main(void) {
  unsigned long tmp = (unsigned long)&g + 4;
  int *pb = (int *)tmp;
  g.b = 7;
  *pb = 5;
  assert(g.b == 5);
  return 0;
}

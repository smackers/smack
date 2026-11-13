#define __VERIFIER_assert annotated_unused_assert
#include "smack.h"
#undef __VERIFIER_assert

// @expect verified
// @flag --clang-options=-DSVCOMP
// @checkbpl awk '/read-only.*summary for check/{x=1}END{exit x}'
// @checkout grep -F "SMACK warning: found loop"

static volatile int effects;

// A reserved name alone is insufficient: this intentionally unannotated
// function has ordinary program effects and must remain an ordinary call.
static void __VERIFIER_assert(int x) { effects += x; }

static void check(const int *a, unsigned n) {
  for (unsigned i = 0; i < n; ++i)
    __VERIFIER_assert(a[i] == 0);
}

int main(void) {
  int a[4];
  check(a, 4);
  return effects;
}

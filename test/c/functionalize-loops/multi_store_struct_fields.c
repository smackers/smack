#include "smack.h"
#include <assert.h>

// @expect verified
// @checkbpl grep -q "functional loop summary for fill"

struct arrays {
  unsigned first[1024];
  unsigned second[1024];
};

static void fill(struct arrays *arrays) {
  unsigned *first = arrays->first;
  unsigned *second = arrays->second;
  for (unsigned i = 0; i < 1024; ++i) {
    first[i] = i;
    second[i] = 0;
  }
}

int main(void) {
  struct arrays arrays;
  unsigned j = __VERIFIER_nondet_unsigned();
  __VERIFIER_assume(j < 1024);
  fill(&arrays);
  assert(arrays.first[j] == j);
  assert(arrays.second[j] == 0);
  return 0;
}

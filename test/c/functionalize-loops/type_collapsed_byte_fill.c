#include "smack.h"
#include <assert.h>

// @expect verified
// @checkbpl grep -q "functional loop summary for fill_bytes"
// @checkout awk '/SMACK warning: found loop/ {x=1} END{exit x}'

struct mixed_fields {
  void *pointer;
  unsigned long count;
};

static void fill_bytes(unsigned char *bytes, unsigned n) {
  for (unsigned i = 0; i < n; ++i)
    bytes[i] = 0;
}

int main(void) {
  struct mixed_fields value;
  unsigned char *bytes = (unsigned char *)&value;
  unsigned index = __VERIFIER_nondet_unsigned();
  __VERIFIER_assume(index < sizeof(value));

  value.pointer = &value;
  value.count = sizeof(value);
  fill_bytes(bytes, sizeof(value));
  assert(bytes[index] == 0);
  return 0;
}

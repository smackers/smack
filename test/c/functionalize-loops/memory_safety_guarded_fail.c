#include "smack.h"

// @expect error
// @flag --check=memory-safety
// @checkbpl grep -q "functional affine access range checks"
// @checkbpl grep -q "functional loop summary for main"

int main(void) {
  unsigned dst[1];
  unsigned enabled[1];
  enabled[0] = 1;
  unsigned *invalid = dst + 1;

  for (unsigned i = 0; i < 1; ++i)
    if (enabled[i] != 0)
      invalid[i] = 1;

  return 0;
}

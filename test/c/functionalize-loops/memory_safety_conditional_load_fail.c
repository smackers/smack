#include "smack.h"

// @expect error
// @flag --check=memory-safety
// @checkbpl grep -q "functional affine access range checks"
// @checkbpl grep -q "functional loop summary for main"
// @checkout awk '/SMACK warning: found loop/ {x=1} END{exit x}'

int main(void) {
  unsigned dst[1];
  unsigned src[1];
  unsigned enabled[1];
  enabled[0] = 1;

  for (unsigned i = 0; i < 1; ++i)
    if (enabled[i] != 0)
      dst[i] = (src + 1)[i];

  return 0;
}

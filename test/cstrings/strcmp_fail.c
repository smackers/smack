
#include <string.h>
#include "smack.h"

// @flag --unroll=5
// @expect error

int main() {
  char *alpha = "alph";
  char *zeta = "zeta";

  int comparison = strcmp(alpha,zeta);

  assert(comparison == 0);
  return 0;
}

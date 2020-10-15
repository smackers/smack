#include "smack.h"
#include <assert.h>
#include <string.h>

// @expect error

int main(void) {
  char *alpha = "alph";
  char *zeta = "zeta";
  int comparison = strcmp(alpha, zeta);

  assert(comparison == 0);
  return 0;
}

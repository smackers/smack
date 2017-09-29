#include <string.h>
#include "smack.h"

// @flag --unroll=5
// @expect error

int main(void) {
  char *string = "ffff";

  size_t firstE = strcspn(string,"f");

  assert(firstE == 5);

  return 0;
}

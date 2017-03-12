
#include <string.h>
#include "smack.h"

// @flag --unroll=5
// @expect error

int main() {
  char *string = "ffff";

  char *firstE = strcspn(string,"f");

  assert(firstE == 5);

  return 0;
}

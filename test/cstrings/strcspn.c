
#include <string.h>
#include "smack.h"

// @flag --unroll=5
// @expect verified 

int main() {
  char *string = "ffef";

  char *firstE = strcspn(string,"f");

  assert(firstE == 2);

  return 0;
}

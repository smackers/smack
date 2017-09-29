#include <string.h>
#include "smack.h"

// @flag --unroll=5
// @expect verified 

int main(void) {
  char *string = "ffef";

  size_t firstE = strcspn(string,"e");

  assert(firstE == 2);

  return 0;
}

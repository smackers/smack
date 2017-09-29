#include <string.h>
#include "smack.h"

// @flag --unroll=5
// @expect error

int main(void) {
  char *notAWebAddress = "word";

  char *dotToEnd = strchr(notAWebAddress,'.');

  assert(dotToEnd != 0); // or assert(dotToEnd);

  return 0;
}

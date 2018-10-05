#include <string.h>
#include "smack.h"

// @expect error

int main(void) {
  char *notAWebAddress = "word";
  char *dotToEnd = strchr(notAWebAddress,'.');

  assert(dotToEnd != 0);
  return 0;
}

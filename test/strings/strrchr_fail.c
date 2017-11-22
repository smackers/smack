#include <string.h>
#include "smack.h"

// @expect error

int main(void) {
  char *website = "a..b";
  char dotCom = strrchr(website,'.');

  assert(strcmp(dotCom,"..b") == 0);
  return 0;
}

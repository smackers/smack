#include <string.h>
#include "smack.h"

// @expect verified

int main(void) {
  char *website = "a..b";
  char *dotCom = strrchr(website,'.');

  assert(strcmp(dotCom,".b") == 0);
  return 0;
}

#include "smack.h"
#include <assert.h>
#include <string.h>

// @expect error

int main(void) {
  char *website = "a..b";
  char dotCom = strrchr(website, '.');

  assert(strcmp(dotCom, "..b") == 0);
  return 0;
}

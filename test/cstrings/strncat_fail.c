
#include <string.h>
#include "smack.h"

// @flag --unroll=5
// @expect error

int main() {
  char dish[30];
  strcpy(dish,"R");

  char *milk = "ice";

  strncat(dish,milk,2);

  assert(strcmp(dish,"Rice") == 0);

  return 0;
}
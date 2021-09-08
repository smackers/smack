#include "smack.h"
#include <assert.h>
#include <string.h>

// @expect verified

int main(void) {
  char dish[40];
  strcpy(dish, "R");

  char *milk = "ice";
  strncat(dish, milk, 2);

  assert(strcmp(dish, "Ric") == 0);
  return 0;
}

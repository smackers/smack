#include "smack.h"
#include <assert.h>
#include <string.h>

// @expect error

int main(void) {
  char dish[30];
  strcpy(dish, "R");

  char *milk = "ice";
  strncat(dish, milk, 2);

  assert(strcmp(dish, "Rice") == 0);
  return 0;
}

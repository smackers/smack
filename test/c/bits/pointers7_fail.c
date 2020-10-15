#include "smack.h"
#include <assert.h>

// @expect error

//	Node Layout
//	int 		0
//	int, char	4
//
struct a {
  int i;
  int j;
};

int main(void) {
  struct a x = {10, 20};
  char *p = (char *)(&(x.j));
  x.i = 2;
  *(p + 1) = 20;
  assert(x.j == 20);
  return 0;
}

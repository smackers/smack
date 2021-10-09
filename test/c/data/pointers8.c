#include "smack.h"
#include <assert.h>

// @expect verified

//	Node Layout
//	long 	0
//	int  	1
//	short	2
//      char	3
int main(void) {
  long int x = 0;
  int *pi = (int *)((char *)(&x) + 1);
  short *ps = (short *)((char *)(&x) + 2);
  char *pc = (char *)((char *)(&x) + 3);
  *pi = 0;
  *ps = 0;
  *pc = 0;
  assert(x == 0);
  return 0;
}

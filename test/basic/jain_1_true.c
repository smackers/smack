#include "smack.h"

// @expect verified

/*extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: goto ERROR;
  }
  return;
}*/
void main()
{
  int y;

  y = 1;

  while(1)
    {
      y = y +2*__VERIFIER_nondet_int();


      assert (y!=0);

    }
}

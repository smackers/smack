#include "smack.h"

// @expect verified

/*extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: goto ERROR;
  }
  return;
}
*/
void main()
{
  int x,y;

  x=0;
  y=4;


  while(1)
    {
      x = x + y;
      y = y +4;


      assert(x!=30);
    }
}

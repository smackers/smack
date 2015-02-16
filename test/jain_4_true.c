#include "smack-defs.h"
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
  int x,y,z;

  x=0;
  y=0;
  z=0;

  while(1)
    {
      x = x +4*__SMACK_nondet();
      y = y +4*__SMACK_nondet();
      z = z +8*__SMACK_nondet();

      assert(x+y+z!=1);
    }
}

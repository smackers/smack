#include "smack.h"

double c_trunc(double x)
{
  union {double f; unsigned long i;} u = {x};
  __VERIFIER_equiv_store_unsigned_long(u.i, 0);
  int e = (int)(u.i >> 52 & 0x7ff) - 0x3ff + 12;
  unsigned long m;

  if (e >= 52 + 12)
    return x;
  if (e < 12)
    e = 1;
  m = -1ULL >> e;
  __VERIFIER_equiv_store_unsigned_long(m, 1);
  __VERIFIER_equiv_store_unsigned_long(u.i & m, 2);
  if ((u.i & m) == 0)
    return x;
  __VERIFIER_equiv_store_unsigned_long(~m, 3);
  __VERIFIER_equiv_store_unsigned_long(u.i & ~m, 4);
  u.i &= ~m;
  __VERIFIER_equiv_store_unsigned_long(u.i, 5);
  return u.f;
}
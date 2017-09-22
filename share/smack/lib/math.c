// This file is distributed under the MIT License. See LICENSE for details.
//
#include <math.h>
#include <smack.h>

//Check the length of pointers
//#if ( __WORDSIZE == 64 )
#if defined(__LP64__) || defined(_LP64)
#define BUILD_64   1
#endif

float fabsf(float x) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := $abs.bvfloat(@);", ret, x);
  return ret;
}

float fdimf(float x, float y) {
  if(x>y)
    return x-y;
  else
    return 0;
}

float roundf(float x) {
  if (__isnan(x) || __isinf(x) || __iszero(x))
    return x;
  double rete = __VERIFIER_nondet_double();
  double reta = __VERIFIER_nondet_double();
  __SMACK_code("@ := sbv32td($round.rne.bvfloat(@));", rete, x);
  __SMACK_code("@ := sbv32td($round.rna.bvfloat(@));", reta, x);
  if (x > 0)
    return fmax(rete, reta);
  return fmin(rete, reta);
}

long lroundf(float x) {
  long ret = __VERIFIER_nondet_long();
  __SMACK_code("@ := $lround.bvfloat(dtf(@));", ret, x);
  return ret;
}

float rintf(float x) {
  return roundf(x);
}

float nearbyintf(float x) {
  return roundf(x);
}

long lrintf(float x) {
  long ret = __VERIFIER_nondet_long();
  __SMACK_code("@ := $lround.bvfloat(dtf(@));", ret, x);
  return ret;
}

float floorf(float x) {
  if (__isnanf(x) || __isinff(x) || __iszerof(x))
    return x;
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := sbv32td($floor.bvfloat(dtf(@)));", ret, x);
  return ret;
}

float ceilf(float x) {
  if (__isnanf(x) || __isinff(x) || __iszerof(x))
    return x;
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := sbv32td($ceil.bvfloat(dtf(@)));", ret, x);
  return ret;
}

float truncf(float x) {
  if (__isnanf(x) || __isinff(x) || __iszerof(x))
    return x;
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := sbv32td($trunc.bvfloat(dtf(@)));", ret, x);
  return ret;
}

float sqrtf(float x) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := $sqrt.bvfloat(dtf(@));", ret, x);
  return ret;
}

float remainderf(float x, float y) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := ftd($rem.bvfloat(dtf(@), dtf(@)));", ret, x, y);
  return ret;
}

float fminf(float x, float y) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := $min.bvfloat(dtf(@), dtf(@));", ret, x, y);
  return ret;
}

float fmaxf(float x, float y) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := $max.bvfloat(dtf(@), dtf(@));", ret, x, y);
  return ret;
}

float fmodf(float x, float y) {
  float result = remainderf(fabsf(x), fabsf(y));
  if (signbitf(result))
    result += fabsf(y);
  return copysignf(result, x);
}

float modff(float x, float* y) {
  *y = floorf(x);
  return x -*y;
}

float copysignf(float x, float y) {
  double ret = __VERIFIER_nondet_double();
  if (__isnegativef(x)^__isnegativef(y))
    __SMACK_code("@ := $fmul.bvfloat(dtf(@), -0e127f24e8);", ret, x);
  else
    ret = x;
  return ret;
}

int __isnormalf(float x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $isnormal.bvfloat(dtf(@)) then 1bv32 else 0bv32;", ret, x);
  return ret;
}

int __isSubnormalf(float x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $issubnormal.bvfloat(dtf(@)) then 1bv32 else 0bv32;", ret, x);
  return ret;
}

int __iszerof(float x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $iszero.bvfloat(dtf(@)) then 1bv32 else 0bv32;", ret, x);
  return ret;
}

int __isinff(float x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $isinfinite.bvfloat(dtf(@)) then 1bv32 else 0bv32;", ret, x);
  return ret;
}

int __isnanf(float x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $isnan.bvfloat(dtf(@)) then 1bv32 else 0bv32;", ret, x);
  return ret;
}

int __isnegativef(float x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $isnegative.bvfloat(dtf(@)) then 1bv32 else 0bv32;", ret, x);
  return ret;
}

int __ispositivef(float x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $ispositive.bvfloat(dtf(@)) then 1bv32 else 0bv32;", ret, x);
  return ret;
}

int __signbitf(float x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if (dtf(@) <= 0e0f24e8) then 1bv32 else 0bv32;", ret, x);
  return ret;
}

int signbitf(float x) {
  return __signbitf(x);
}

int __fpclassifyf(float x) {
  if (__isnanf(x))
    return 0;
  if (__isinff(x))
    return 1;
  if (__iszerof(x))
    return 2;
  if (__isSubnormalf(x))
    return 3;
  return 4;
}

int fpclassifyf(float x) {
  return __fpclassifyf(x);
}

int __finitef(float x) {
  return !__isinf(x) && !__isnanf(x);
}

double fabs(double x) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := $abs.bvdouble(@);", ret, x);
  return ret;
}

double fdim(double x, double y) {
  if(x>y)
    return x-y;
  else
    return 0;
}

double round(double x) {
  if (__isnan(x) || __isinf(x) || __iszero(x))
    return x;
  double rete = __VERIFIER_nondet_double();
  double reta = __VERIFIER_nondet_double();
  __SMACK_code("@ := sbv64td($round.rne.bvdouble(@));", rete, x);
  __SMACK_code("@ := sbv64td($round.rna.bvdouble(@));", reta, x);
  if (x > 0)
    return fmax(rete, reta);
  return fmin(rete, reta);
}

long lround(double x) {
  long ret = __VERIFIER_nondet_long();
  __SMACK_code("@ := $lround.bvdouble(@);", ret, x);
  return ret;
}

double rint(double x) {
  return round(x);
}

double nearbyint(double x) {
  return round(x);
}

long lrint(double x) {
  return lround(x);
}

double floor(double x) {
  if (__isnan(x) || __isinf(x) || __iszero(x))
    return x;
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := sbv64td($floor.bvdouble(@));", ret, x);
  return ret;
}

double ceil(double x) {
  if (__isnan(x) || __isinf(x) || __iszero(x))
    return x;
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := sbv64td($ceil.bvdouble(@));", ret, x);
  return ret;
}

double trunc(double x) {
  if (__isnan(x) || __isinf(x) || __iszero(x))
    return x;
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := sbv64td($trunc.bvdouble(@));", ret, x);
  return ret;
}

double sqrt(double x) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := $sqrt.bvdouble(@);", ret, x);
  return ret;
}

double remainder(double x, double y) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := ftd(dtf($rem.bvdouble(ftd(dtf(@)), ftd(dtf(@)))));", ret, x, y);
  return ret;
}

double fmin(double x, double y) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := $min.bvdouble(@, @);", ret, x, y);
  return ret;
}

double fmax(double x, double y) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := $max.bvdouble(@, @);", ret, x, y);
  return ret;
}

double fmod(double x, double y) {
  double result = remainder(fabs(x), fabs(y));
  if (signbit(result))
    result += fabs(y);
  return copysign(result, x);
}

double modf(double x, double* y) {
  *y = floor(x);
  return x - *y;
}

double copysign(double x, double y) {
  double ret = __VERIFIER_nondet_double();
  if (__isnegative(x)^__isnegative(y))
    __SMACK_code("@ := $fmul.bvdouble(@, -0e1023f53e11);", ret, x);
  else
    ret = x;
  return ret;
}

double nan(const char* x) {
  return 0.0/0.0;
}

int __isnormal(double x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $isnormal.bvdouble(@) then 1bv32 else 0bv32;", ret, x);
  return ret;
}

int __isSubnormal(double x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $issubnormal.bvdouble(@) then 1bv32 else 0bv32;", ret, x);
  return ret;
}

int __iszero(double x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $iszero.bvdouble(@) then 1bv32 else 0bv32;", ret, x);
  return ret;
}

int __isinf(double x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $isinfinite.bvdouble(@) then 1bv32 else 0bv32;", ret, x);
  return ret;
}

int __isnan(double x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $isnan.bvdouble(@) then 1bv32 else 0bv32;", ret, x);
  return ret;
}

int __isnegative(double x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $isnegative.bvdouble(@) then 1bv32 else 0bv32;", ret, x);
  return ret;
}

int __ispositive(double x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $ispositive.bvdouble(@) then 1bv32 else 0bv32;", ret, x);
  return ret;
}

int __signbit(double x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if (@ <= 0e0f53e11) then 1bv32 else 0bv32;", ret, x);
  return ret;
}

int signbit(double x) {
  return __signbit(x);
}

int __fpclassify(double x) {
  if (__isnan(x))
    return 0;
  if (__isinf(x))
    return 1;
  if (__iszero(x))
    return 2;
  if (__isSubnormal(x))
    return 3;
  return 4;
}

int fpclassify(double x) {
  return __fpclassify(x);
}

int __finite(double x) {
  return !__isinf(x) && !__isnan(x);
}

/*int __isnormall(long double x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $isnormal.bvlongdouble(@) then 1bv32 else 0bv32;", ret, x);
  return ret;
}

int __isSubnormall(long double x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $issubnormal.bvlongdouble(@) then 1bv32 else 0bv32;", ret, x);
  return ret;
}

int __iszerol(long double x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $iszero.bvlongdouble(@) then 1bv32 else 0bv32;", ret, x);
  return ret;
}

int __isinfl(long double x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $isinfinite.bvlongdouble(@) then 1bv32 else 0bv32;", ret, x);
  return ret;
}

int __isnanl(long double x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $isnan.bvlongdouble(@) then 1bv32 else 0bv32;", ret, x);
  return ret;
}

int __isnegativel(long double x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $isnegative.bvlongdouble(@) then 1bv32 else 0bv32;", ret, x);
  return ret;
}

int __ispositivel(long double x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $ispositive.bvlongdouble(@) then 1bv32 else 0bv32;", ret, x);
  return ret;
}

int __signbitl(long double x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if (@ <= 0e0f53e11) then 1bv32 else 0bv32;", ret, x);
  return ret;
}

int signbitl(long double x) {
  return __signbitl(x);
}

int __fpclassifyl(long double x) {
  if (__isnanl(x))
    return 0;
  if (__isinfl(x))
    return 1;
  if (__iszerol(x))
    return 2;
  if (__isSubnormall(x))
    return 3;
  return 4;
}

int fpclassifyl(long double x) {
  return __fpclassifyl(x);
}

int __finitel(long double x) {
  return !__isinfl(x) && !__isnanl(x);
}*/

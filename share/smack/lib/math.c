// This file is distributed under the MIT License. See LICENSE for details.
//
#include <math.h>
#include <smack.h>

//Check the length of pointers
//#if ( __WORDSIZE == 64 )
#if defined(__LP64__) || defined(_LP64)
#define BUILD_64 1
#endif

float fabsf(float x) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := ftd($abs.bvfloat(dtf(@)));", ret, x);
  return ret;
}

float fdimf(float x, float y) {
  if (__isnanf(x) || __isnanf(y)) {
    return nanf(0);
  }
  double val = __VERIFIER_nondet_double();
  __SMACK_code("@ := ftd($fsub.bvfloat(dtf(@), dtf(@)));", val, x, y);
  return fmaxf(0.0f, val);
}

float roundf(float x) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := ftd($round.bvfloat(dtf(@)));", ret, x);
  return ret;
}

long lroundf(float x) {
  return roundf(x);
}

float rintf(float x) {
  return roundf(x);
}

float nearbyintf(float x) {
  return roundf(x);
}

long lrintf(float x) {
  return roundf(x);
}

float floorf(float x) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := ftd($floor.bvfloat(dtf(@)));", ret, x);
  return ret;
}

float ceilf(float x) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := ftd($ceil.bvfloat(dtf(@)));", ret, x);
  return ret;
}

float truncf(float x) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := ftd($trunc.bvfloat(dtf(@)));", ret, x);
  return ret;
}

float sqrtf(float x) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := ftd($sqrt.bvfloat(dtf(@)));", ret, x);
  return ret;
}

float remainderf(float x, float y) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := ftd($frem.bvfloat(dtf(@), dtf(@)));", ret, x, y);
  return ret;
}

float fminf(float x, float y) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := ftd($min.bvfloat(dtf(@), dtf(@)));", ret, x, y);
  return ret;
}

float fmaxf(float x, float y) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := ftd($max.bvfloat(dtf(@), dtf(@)));", ret, x, y);
  return ret;
}

float fmodf(float x, float y) {
   if (__isnanf(x) || __isnanf(y) || __isinff(x) || __iszerof(y)) {
    return nanf(0);
  }
  double ret = __VERIFIER_nondet_double();
  y = fabsf(y);
  ret = remainderf(fabsf(x), y);
  if (__signbitf(ret)) {
    __SMACK_code("@ := ftd($fadd.bvfloat(dtf(@), dtf(@)));", ret, ret, y);
  }
  return copysignf(ret, x);
}

float modff(float x, float *iPart) {
  double fPart = __VERIFIER_nondet_double();
  if (__isinff(x)) {
    *iPart = x;
    fPart = 0.0f;
  } else {
    *iPart = truncf(x);
    fPart = __VERIFIER_nondet_double();
    __SMACK_code("@ := ftd($fsub.bvdouble(dtf(@), dtf(@)));", fPart, x, *iPart);
  }
  if (__iszerof(fPart)) {
    fPart = __signbitf(x) ? -0.0f : 0.0f;
  }
  return fPart;
}

float copysignf(float x, float y) {
  if (__signbitf(x) - __signbitf(y)) {
    return -x;
  } else {
    return x;
  }
}

float nanf(const char *c) {
  return 0.0f / 0.0f;
}

int __isnormalf(float x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $isnormal.bvfloat.bool(dtf(@)) then $1 else $0;", ret, x);
  return ret;
}

int __issubnormalf(float x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $issubnormal.bvfloat.bool(dtf(@)) then $1 else $0;", ret, x);
  return ret;
}

int __iszerof(float x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $iszero.bvfloat.bool(dtf(@)) then $1 else $0;", ret, x);
  return ret;
}

int __isinff(float x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $isinfinite.bvfloat.bool(dtf(@)) then $1 else $0;", ret, x);
  return ret;
}

int __isnanf(float x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $isnan.bvfloat.bool(dtf(@)) then $1 else $0;", ret, x);
  return ret;
}

int __signbitf(float x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $isnegative.bvfloat.bool(dtf(@)) then $1 else $0;", ret, x);
  return ret;
}

int __fpclassifyf(float x) {
  if (__isnanf(x))
    return 0;
  if (__isinff(x))
    return 1;
  if (__iszerof(x))
    return 2;
  if (__issubnormalf(x))
    return 3;
  return 4;
}

int __isfinitef(float x) {
  return !__isinff(x) && !__isnanf(x);
}

double fabs(double x) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := $abs.bvdouble(@);", ret, x);
  return ret;
}

double fdim(double x, double y) {
  if (__isnan(x) || __isnan(y)) {
    return nan(0);
  }
  double val = __VERIFIER_nondet_double();
  __SMACK_code("@ := $fsub.bvdouble(@, @);", val, x, y);
  return fmax(0.0, val);
}

double round(double x) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := $round.bvdouble(@);", ret, x);
  return ret;
}

long lround(double x) {
  return round(x);
}

double rint(double x) {
  return round(x);
}

double nearbyint(double x) {
  return round(x);
}

long lrint(double x) {
  return round(x);
}

double floor(double x) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := $floor.bvdouble(@);", ret, x);
  return ret;
}

double ceil(double x) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := $ceil.bvdouble(@);", ret, x);
  return ret;
}

double trunc(double x) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := $trunc.bvdouble(@);", ret, x);
  return ret;
}

double sqrt(double x) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := $sqrt.bvdouble(@);", ret, x);
  return ret;
}

double remainder(double x, double y) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := $frem.bvdouble(@, @);", ret, x, y);
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
  if (__isnan(x) || __isnan(y) || __isinf(x) || __iszero(y)) {
    return nan(0);
  }
  double ret = __VERIFIER_nondet_double();
  y = fabs(y);
  ret = remainder(fabs(x), y);
  if (__signbit(ret)) {
    __SMACK_code("@ := $fadd.bvdouble(@, @);", ret, ret, y);
  }
  return copysign(ret, x);
}

double modf(double x, double *iPart) {
  double fPart = __VERIFIER_nondet_double();
  if (__isinf(x)) {
    *iPart = x;
    fPart = 0.0;
  } else {
    *iPart = trunc(x);
    fPart = __VERIFIER_nondet_double();
    __SMACK_code("@ := $fsub.bvdouble(@, @);", fPart, x, *iPart);
  }
  if (__iszero(fPart)) {
    fPart = (__signbit(x)) ? -0.0 : 0.0;
  }
  return fPart;
}

double copysign(double x, double y) {
  if (__signbit(x) - __signbit(y)) {
    return -x;
  } else {
    return x;
  }
}

double nan(const char *x) {
  return 0.0 / 0.0;
}

int __isnormal(double x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $isnormal.bvdouble.bool(@) then $1 else $0;", ret, x);
  return ret;
}

int __issubnormal(double x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $issubnormal.bvdouble.bool(@) then $1 else $0;", ret, x);
  return ret;
}

int __iszero(double x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $iszero.bvdouble.bool(@) then $1 else $0;", ret, x);
  return ret;
}

int __isinf(double x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $isinfinite.bvdouble.bool(@) then $1 else $0;", ret, x);
  return ret;
}

int __isnan(double x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $isnan.bvdouble.bool(@) then $1 else $0;", ret, x);
  return ret;
}

int __signbit(double x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $isnegative.bvdouble.bool(@) then $1 else $0;", ret, x);
  return ret;
}

int __fpclassify(double x) {
  if (__isnan(x))
    return 0;
  if (__isinf(x))
    return 1;
  if (__iszero(x))
    return 2;
  if (__issubnormal(x))
    return 3;
  return 4;
}

int __isfinite(double x) {
  return !__isinf(x) & !__isnan(x);
}

/*int __isnormall(long double x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $isnormal.bvlongdouble.bool(@) then $1 else $0;", ret, x);
  return ret;
  }

  int __issubnormall(long double x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $issubnormal.bvlongdouble.bool(@) then $1 else $0;", ret, x);
  return ret;
  }

  int __iszerol(long double x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $iszero.bvlongdouble.bool(@) then $1 else $0;", ret, x);
  return ret;
  }

  int __isinfl(long double x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $isinfinite.bvlongdouble.bool(@) then $1 else $0;", ret, x);
  return ret;
  }

  int __isnanl(long double x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $isnan.bvlongdouble.bool(@) then $1 else $0;", ret, x);
  return ret;
  }

  int __signbitl(long double x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $isnegative.bvlongdouble.bool(@) then $1 else $0;", ret, x);
  return ret;
  }

  int __fpclassifyl(long double x) {
  if (__isnanl(x))
  return 0;
  if (__isinfl(x))
  return 1;
  if (__iszerol(x))
  return 2;
  if (__issubnormall(x))
  return 3;
  return 4;
  }

  int __isfinitel(long double x) {
  return !__isinfl(x) && !__isnanl(x);
  }*/

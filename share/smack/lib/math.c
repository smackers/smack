//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include <math.h>
#include <smack.h>

float fabsf(float x) {
  float ret = __VERIFIER_nondet_float();
  __SMACK_code("@f := $abs.bvfloat(@f);", ret, x);
  return ret;
}

float fdimf(float x, float y) {
  if (__isnanf(x) || __isnanf(y)) {
    return nanf(0);
  }
  float val = __VERIFIER_nondet_float();
  __SMACK_code("@f := $fsub.bvfloat($rmode, @f, @f);", val, x, y);
  return fmaxf(0.0f, val);
}

float roundf(float x) {
  float ret = __VERIFIER_nondet_float();
  __SMACK_code("@f := $round.bvfloat(RNA, @f);", ret, x);
  return ret;
}

long lroundf(float x) { return roundf(x); }

float rintf(float x) {
  float ret = __VERIFIER_nondet_float();
  __SMACK_code("@f := $round.bvfloat($rmode, @f);", ret, x);
  return ret;
}

float nearbyintf(float x) {
  float ret = __VERIFIER_nondet_float();
  __SMACK_code("@f := $round.bvfloat($rmode, @f);", ret, x);
  return ret;
}

long lrintf(float x) { return rintf(x); }

float floorf(float x) {
  float ret = __VERIFIER_nondet_float();
  __SMACK_code("@f := $round.bvfloat(RTN, @f);", ret, x);
  return ret;
}

float ceilf(float x) {
  float ret = __VERIFIER_nondet_float();
  __SMACK_code("@f := $round.bvfloat(RTP, @f);", ret, x);
  return ret;
}

float truncf(float x) {
  float ret = __VERIFIER_nondet_float();
  __SMACK_code("@f := $round.bvfloat(RTZ, @f);", ret, x);
  return ret;
}

float sqrtf(float x) {
  float ret = __VERIFIER_nondet_float();
  __SMACK_code("@f := $sqrt.bvfloat($rmode, @f);", ret, x);
  return ret;
}

float remainderf(float x, float y) {
  float ret = __VERIFIER_nondet_float();
  __SMACK_code("@f := $frem.bvfloat(@f, @f);", ret, x, y);
  return ret;
}

float fminf(float x, float y) {
  float ret = __VERIFIER_nondet_float();
  __SMACK_code("@f := $min.bvfloat(@f, @f);", ret, x, y);
  return ret;
}

float fmaxf(float x, float y) {
  float ret = __VERIFIER_nondet_float();
  __SMACK_code("@f := $max.bvfloat(@f, @f);", ret, x, y);
  return ret;
}

float fmodf(float x, float y) {
  if (__isnanf(x) || __isnanf(y) || __isinff(x) || __iszerof(y)) {
    return nanf(0);
  }
  float ret = __VERIFIER_nondet_float();
  y = fabsf(y);
  ret = remainderf(fabsf(x), y);
  if (__signbitf(ret)) {
    __SMACK_code("@f := $fadd.bvfloat($rmode, @f, @f);", ret, ret, y);
  }
  return copysignf(ret, x);
}

float modff(float x, float *iPart) {
  float fPart = __VERIFIER_nondet_float();
  if (__isinff(x)) {
    *iPart = x;
    fPart = 0.0f;
  } else {
    *iPart = truncf(x);
    __SMACK_code("@f := $fsub.bvfloat($rmode, @f, @f);", fPart, x, *iPart);
  }
  if (__iszerof(fPart)) {
    fPart = __signbitf(x) ? -0.0f : 0.0f;
  }
  return fPart;
}

float copysignf(float x, float y) {
  if (__signbitf(x) != __signbitf(y)) {
    fi u;
    u.f = x;
    u.i.sign ^= 1;
    x = u.f;
  }
  return x;
}

float nanf(const char *c) { return 0.0f / 0.0f; }

int __isnormalf(float x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $isnormal.bvfloat.bool(@f) then $1 else $0;", ret, x);
  return ret;
}

int __issubnormalf(float x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $issubnormal.bvfloat.bool(@f) then $1 else $0;", ret,
               x);
  return ret;
}

int __iszerof(float x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $iszero.bvfloat.bool(@f) then $1 else $0;", ret, x);
  return ret;
}

int __isinff(float x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $isinfinite.bvfloat.bool(@f) then $1 else $0;", ret, x);
  return ret;
}

int __isnanf(float x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $isnan.bvfloat.bool(@f) then $1 else $0;", ret, x);
  return ret;
}

int __signbitf(float x) {
  fi u;
  u.f = x;
  return u.i.sign;
}

int __fpclassifyf(float x) {
  if (__isnanf(x))
    return FP_NAN;
  if (__isinff(x))
    return FP_INFINITE;
  if (__iszerof(x))
    return FP_ZERO;
  if (__issubnormalf(x))
    return FP_SUBNORMAL;
  return FP_NORMAL;
}

int __finitef(float x) { return !__isinff(x) && !__isnanf(x); }

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
  __SMACK_code("@ := $fsub.bvdouble($rmode, @, @);", val, x, y);
  return fmax(0.0, val);
}

double round(double x) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := $round.bvdouble(RNA, @);", ret, x);
  return ret;
}

long lround(double x) { return round(x); }

double rint(double x) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := $round.bvdouble($rmode, @);", ret, x);
  return ret;
}

double nearbyint(double x) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := $round.bvdouble($rmode, @);", ret, x);
  return ret;
}

long lrint(double x) { return rint(x); }

double floor(double x) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := $round.bvdouble(RTN, @);", ret, x);
  return ret;
}

double ceil(double x) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := $round.bvdouble(RTP, @);", ret, x);
  return ret;
}

double trunc(double x) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := $round.bvdouble(RTZ, @);", ret, x);
  return ret;
}

double sqrt(double x) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := $sqrt.bvdouble($rmode, @);", ret, x);
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
    __SMACK_code("@ := $fadd.bvdouble($rmode, @, @);", ret, ret, y);
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
    __SMACK_code("@ := $fsub.bvdouble($rmode, @, @);", fPart, x, *iPart);
  }
  if (__iszero(fPart)) {
    fPart = (__signbit(x)) ? -0.0 : 0.0;
  }
  return fPart;
}

double copysign(double x, double y) {
  if (__signbit(x) != __signbit(y)) {
    di u;
    u.d = x;
    u.i.sign ^= 1;
    x = u.d;
  }
  return x;
}

double nan(const char *x) { return 0.0 / 0.0; }

int __isnormal(double x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $isnormal.bvdouble.bool(@) then $1 else $0;", ret, x);
  return ret;
}

int __issubnormal(double x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $issubnormal.bvdouble.bool(@) then $1 else $0;", ret,
               x);
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
  di u;
  u.d = x;
  return u.i.sign;
}

int __fpclassify(double x) {
  if (__isnan(x))
    return FP_NAN;
  if (__isinf(x))
    return FP_INFINITE;
  if (__iszero(x))
    return FP_ZERO;
  if (__issubnormal(x))
    return FP_SUBNORMAL;
  return FP_NORMAL;
}

int __finite(double x) { return !__isinf(x) && !__isnan(x); }

long double fabsl(long double x) {
  long double ret = __VERIFIER_nondet_long_double();
  __SMACK_code("@ := $abs.bvlongdouble(@);", ret, x);
  return ret;
}

long double fdiml(long double x, long double y) {
  if (__isnanl(x) || __isnanl(y)) {
    return nanl(0);
  }
  long double val = __VERIFIER_nondet_long_double();
  __SMACK_code("@ := $fsub.bvlongdouble($rmode, @, @);", val, x, y);
  return fmaxl(0.0l, val);
}

long double roundl(long double x) {
  long double ret = __VERIFIER_nondet_long_double();
  __SMACK_code("@ := $round.bvlongdouble(RNA, @);", ret, x);
  return ret;
}

long lroundl(long double x) { return roundl(x); }

long double rintl(long double x) {
  long double ret = __VERIFIER_nondet_long_double();
  __SMACK_code("@ := $round.bvlongdouble($rmode, @);", ret, x);
  return ret;
}

long double nearbyintl(long double x) {
  long double ret = __VERIFIER_nondet_long_double();
  __SMACK_code("@ := $round.bvlongdouble($rmode, @);", ret, x);
  return ret;
}

long lrintl(long double x) { return rintl(x); }

long double floorl(long double x) {
  long double ret = __VERIFIER_nondet_long_double();
  __SMACK_code("@ := $round.bvlongdouble(RTN, @);", ret, x);
  return ret;
}

long double ceill(long double x) {
  long double ret = __VERIFIER_nondet_long_double();
  __SMACK_code("@ := $round.bvlongdouble(RTP, @);", ret, x);
  return ret;
}

long double truncl(long double x) {
  long double ret = __VERIFIER_nondet_long_double();
  __SMACK_code("@ := $round.bvlongdouble(RTZ, @);", ret, x);
  return ret;
}

long double sqrtl(long double x) {
  long double ret = __VERIFIER_nondet_long_double();
  __SMACK_code("@ := $sqrt.bvlongdouble($rmode, @);", ret, x);
  return ret;
}

long double remainderl(long double x, long double y) {
  long double ret = __VERIFIER_nondet_long_double();
  __SMACK_code("@ := $frem.bvlongdouble(@, @);", ret, x, y);
  return ret;
}

long double fminl(long double x, long double y) {
  long double ret = __VERIFIER_nondet_long_double();
  __SMACK_code("@ := $min.bvlongdouble(@, @);", ret, x, y);
  return ret;
}

long double fmaxl(long double x, long double y) {
  long double ret = __VERIFIER_nondet_long_double();
  __SMACK_code("@ := $max.bvlongdouble(@, @);", ret, x, y);
  return ret;
}

long double fmodl(long double x, long double y) {
  if (__isnanl(x) || __isnanl(y) || __isinfl(x) || __iszerol(y)) {
    return nanl(0);
  }
  long double ret = __VERIFIER_nondet_long_double();
  y = fabsl(y);
  ret = remainderl(fabsl(x), y);
  if (__signbitl(ret)) {
    __SMACK_code("@ := $fadd.bvlongdouble($rmode, @, @);", ret, ret, y);
  }
  return copysignl(ret, x);
}

long double modfl(long double x, long double *iPart) {
  long double fPart = __VERIFIER_nondet_long_double();
  if (__isinfl(x)) {
    *iPart = x;
    fPart = 0.0l;
  } else {
    *iPart = truncl(x);
    __SMACK_code("@ := $fsub.bvlongdouble($rmode, @, @);", fPart, x, *iPart);
  }
  if (__iszerol(fPart)) {
    fPart = __signbitl(x) ? -0.0l : 0.0l;
  }
  return fPart;
}

long double copysignl(long double x, long double y) {
  if (__signbitl(x) != __signbitl(y)) {
    li u;
    u.l = x;
    u.i.sign ^= 1;
    x = u.l;
  }
  return x;
}

long double nanl(const char *c) { return 0.0l / 0.0l; }

int __isnormall(long double x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $isnormal.bvlongdouble.bool(@) then $1 else $0;", ret,
               x);
  return ret;
}

int __issubnormall(long double x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $issubnormal.bvlongdouble.bool(@) then $1 else $0;",
               ret, x);
  return ret;
}

int __iszerol(long double x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $iszero.bvlongdouble.bool(@) then $1 else $0;", ret, x);
  return ret;
}

int __isinfl(long double x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $isinfinite.bvlongdouble.bool(@) then $1 else $0;", ret,
               x);
  return ret;
}

int __isnanl(long double x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $isnan.bvlongdouble.bool(@) then $1 else $0;", ret, x);
  return ret;
}

int __signbitl(long double x) {
  li u;
  u.l = x;
  return u.i.sign;
}

int __fpclassifyl(long double x) {
  if (__isnanl(x))
    return FP_NAN;
  if (__isinfl(x))
    return FP_INFINITE;
  if (__iszerol(x))
    return FP_ZERO;
  if (__issubnormall(x))
    return FP_SUBNORMAL;
  return FP_NORMAL;
}

int __finitel(long double x) { return !__isinfl(x) && !__isnanl(x); }

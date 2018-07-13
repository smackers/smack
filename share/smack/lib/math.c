// This file is distributed under the MIT License. See LICENSE for details.
//
#include <math.h>
#include <smack.h>

float fabsf(float x) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := ftd($rmode, $abs.bvfloat(dtf($rmode, @)));", ret, x);
  return ret;
}

float fdimf(float x, float y) {
  if (__isnanf(x) || __isnanf(y)) {
    return nanf(0);
  }
  double val = __VERIFIER_nondet_double();
  __SMACK_code("@ := ftd($rmode, $fsub.bvfloat($rmode, dtf($rmode, @), dtf($rmode, @)));", val, x, y);
  return fmaxf(0.0f, val);
}

float roundf(float x) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := ftd($rmode, $round.bvfloat(RNA, dtf($rmode, @)));", ret, x);
  return ret;
}

long lroundf(float x) {
  return roundf(x);
}

float rintf(float x) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := ftd($rmode, $round.bvfloat($rmode, dtf($rmode, @)));", ret, x);
  return ret;
}

float nearbyintf(float x) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := ftd($rmode, $round.bvfloat($rmode, dtf($rmode, @)));", ret, x);
  return ret;
}

long lrintf(float x) {
  return rintf(x);
}

float floorf(float x) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := ftd($rmode, $round.bvfloat(RTN, dtf($rmode, @)));", ret, x);
  return ret;
}

float ceilf(float x) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := ftd($rmode, $round.bvfloat(RTP, dtf($rmode, @)));", ret, x);
  return ret;
}

float truncf(float x) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := ftd($rmode, $round.bvfloat(RTZ, dtf($rmode, @)));", ret, x);
  return ret;
}

float sqrtf(float x) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := ftd($rmode, $sqrt.bvfloat($rmode, dtf($rmode, @)));", ret, x);
  return ret;
}

float remainderf(float x, float y) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := ftd($rmode, $frem.bvfloat(dtf($rmode, @), dtf($rmode, @)));", ret, x, y);
  return ret;
}

float fminf(float x, float y) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := ftd($rmode, $min.bvfloat(dtf($rmode, @), dtf($rmode, @)));", ret, x, y);
  return ret;
}

float fmaxf(float x, float y) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := ftd($rmode, $max.bvfloat(dtf($rmode, @), dtf($rmode, @)));", ret, x, y);
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
    __SMACK_code("@ := ftd($rmode, $fadd.bvfloat($rmode, dtf($rmode, @), dtf($rmode, @)));", ret, ret, y);
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
    __SMACK_code("@ := ftd($rmode, $fsub.bvdouble($rmode, dtf($rmode, @), dtf($rmode, @)));", fPart, x, *iPart);
  }
  if (__iszerof(fPart)) {
    fPart = __signbitf(x) ? -0.0f : 0.0f;
  }
  return fPart;
}

float copysignf(float x, float y) {
  if (__signbitf(x) != __signbitf(y)) {
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
  __SMACK_code("@ := if $isnormal.bvfloat.bool(dtf($rmode, @)) then $1 else $0;", ret, x);
  return ret;
}

int __issubnormalf(float x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $issubnormal.bvfloat.bool(dtf($rmode, @)) then $1 else $0;", ret, x);
  return ret;
}

int __iszerof(float x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $iszero.bvfloat.bool(dtf($rmode, @)) then $1 else $0;", ret, x);
  return ret;
}

int __isinff(float x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $isinfinite.bvfloat.bool(dtf($rmode, @)) then $1 else $0;", ret, x);
  return ret;
}

int __isnanf(float x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $isnan.bvfloat.bool(dtf($rmode, @)) then $1 else $0;", ret, x);
  return ret;
}

int __signbitf(float x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $isnegative.bvfloat.bool(dtf($rmode, @)) then $1 else $0;", ret, x);
  return ret;
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

int __finitef(float x) {
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
  __SMACK_code("@ := $fsub.bvdouble($rmode, @, @);", val, x, y);
  return fmax(0.0, val);
}

double round(double x) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := $round.bvdouble(RNA, @);", ret, x);
  return ret;
}

long lround(double x) {
  return round(x);
}

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

long lrint(double x) {
  return rint(x);
}

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
    fPart = __VERIFIER_nondet_double();
    __SMACK_code("@ := $fsub.bvdouble($rmode, @, @);", fPart, x, *iPart);
  }
  if (__iszero(fPart)) {
    fPart = (__signbit(x)) ? -0.0 : 0.0;
  }
  return fPart;
}

double copysign(double x, double y) {
  if (__signbit(x) != __signbit(y)) {
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
    return FP_NAN;
  if (__isinf(x))
    return FP_INFINITE;
  if (__iszero(x))
    return FP_ZERO;
  if (__issubnormal(x))
    return FP_SUBNORMAL;
  return FP_NORMAL;
}

int __finite(double x) {
  return !__isinf(x) && !__isnan(x);
}

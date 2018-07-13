// This file is distributed under the MIT License. See LICENSE for details.
//

#ifndef MATH_H
#define MATH_H

enum
  {
    FP_NAN,
# define FP_NAN FP_NAN
    FP_INFINITE,
# define FP_INFINITE FP_INFINITE
    FP_ZERO,
# define FP_ZERO FP_ZERO
    FP_SUBNORMAL,
# define FP_SUBNORMAL FP_SUBNORMAL
    FP_NORMAL
# define FP_NORMAL FP_NORMAL
  };

#define fpclassify(x) (sizeof(x) == sizeof(float) ? __fpclassifyf(x) : __fpclassify(x))
#define signbit(x) (sizeof(x) == sizeof(float) ? __signbitf(x) : __signbit(x))
#define isfinite(x) (sizeof(x) == sizeof(float) ? __finitef(x) : __finite(x))
#define isnormal(x) (sizeof(x) == sizeof(float) ? __isnormalf(x) : __isnormal(x))
#define isnan(x) (sizeof(x) == sizeof(float) ? __isnanf(x) : __isnan(x))
#define isinf(x) (sizeof(x) == sizeof(float) ? __isinff(x) : __isinf(x))

float fabsf(float x);
float fdimf(float x, float y);
float roundf(float x);
long lroundf(float x);
float rintf(float x);
float nearbyintf(float x);
long lrintf(float x);
float floorf(float x);
float ceilf(float x);
float truncf(float x);
float sqrtf(float x);
float remainderf(float x, float y);
float fminf(float x, float y);
float fmaxf(float x, float y);
float fmodf(float x, float y);
float modff(float x, float* y);
float copysignf(float x, float y);
float nanf(const char* x);
int __isnormalf(float x);
int __issubnormalf(float x);
int __iszerof(float x);
int __isinff(float x);
int __isnanf(float x);
int __isnegativef(float x);
int __signbitf(float x);
int __fpclassifyf(float x);
int __finitef(float x);

double fabs(double x);
double fdim(double x, double y);
double round(double x);
long lround(double x);
double rint(double x);
double nearbyint(double x);
long lrint(double x);
double floor(double x);
double ceil(double x);
double trunc(double x);
double sqrt(double x);
double remainder(double x, double y);
double fmin(double x, double y);
double fmax(double x, double y);
double fmod(double x, double y);
double modf(double x, double* y);
double copysign(double x, double y);
double nan(const char* x);
int __isnormal(double x);
int __issubnormal(double x);
int __iszero(double x);
int __isinf(double x);
int __isnan(double x);
int __isnegative(double x);
int __signbit(double x);
int __fpclassify(double x);
int __finite(double x);

#endif

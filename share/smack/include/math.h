//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef MATH_H
#define MATH_H

#define FP_NAN 0
#define FP_INFINITE 1
#define FP_ZERO 2
#define FP_SUBNORMAL 3
#define FP_NORMAL 4

#define isnormal(x)                                                            \
  (sizeof(x) == sizeof(long double) ? __isnormall(x)                           \
   : sizeof(x) == sizeof(double)    ? __isnormal(x)                            \
                                    : __isnormalf(x))
#define isinf(x)                                                               \
  (sizeof(x) == sizeof(long double) ? __isinfl(x)                              \
   : sizeof(x) == sizeof(double)    ? __isinf(x)                               \
                                    : __isinff(x))
#define isnan(x)                                                               \
  (sizeof(x) == sizeof(long double) ? __isnanl(x)                              \
   : sizeof(x) == sizeof(double)    ? __isnan(x)                               \
                                    : __isnanf(x))
#define signbit(x)                                                             \
  (sizeof(x) == sizeof(long double) ? __signbitl(x)                            \
   : sizeof(x) == sizeof(double)    ? __signbit(x)                             \
                                    : __signbitf(x))
#define fpclassify(x)                                                          \
  (sizeof(x) == sizeof(long double) ? __fpclassifyl(x)                         \
   : sizeof(x) == sizeof(double)    ? __fpclassify(x)                          \
                                    : __fpclassifyf(x))
#define isfinite(x)                                                            \
  (sizeof(x) == sizeof(long double) ? __finitel(x)                             \
   : sizeof(x) == sizeof(double)    ? __finite(x)                              \
                                    : __finitef(x))

typedef union {
  float f;
  struct {
    unsigned sigAndExp : 31;
    unsigned sign : 1;
  } i;
} fi;

typedef union {
  double d;
  struct {
    unsigned sigAndExpLower : 32;
    unsigned sigAndExpUpper : 31;
    unsigned sign : 1;
  } i;
} di;

typedef union {
  long double l;
  struct {
    unsigned sigAndExpLower : 32;
    unsigned sigAndExpMiddle : 32;
    unsigned sigAndExpUpper : 15;
    unsigned sign : 1;
  } i;
} li;

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
float modff(float x, float *y);
float copysignf(float x, float y);
float nanf(const char *x);
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
double modf(double x, double *y);
double copysign(double x, double y);
double nan(const char *x);
int __isnormal(double x);
int __issubnormal(double x);
int __iszero(double x);
int __isinf(double x);
int __isnan(double x);
int __isnegative(double x);
int __signbit(double x);
int __fpclassify(double x);
int __finite(double x);

long double fabsl(long double x);
long double fdiml(long double x, long double y);
long double roundl(long double x);
long lroundl(long double x);
long double rintl(long double x);
long double nearbyintl(long double x);
long lrintl(long double x);
long double floorl(long double x);
long double ceill(long double x);
long double truncl(long double x);
long double sqrtl(long double x);
long double remainderl(long double x, long double y);
long double fminl(long double x, long double y);
long double fmaxl(long double x, long double y);
long double fmodl(long double x, long double y);
long double modfl(long double x, long double *y);
long double copysignl(long double x, long double y);
long double nanl(const char *x);
int __isnormall(long double x);
int __issubnormall(long double x);
int __iszerol(long double x);
int __isinfl(long double x);
int __isnanl(long double x);
int __isnegativel(long double x);
int __signbitl(long double x);
int __fpclassifyl(long double x);
int __finitel(long double x);

#endif

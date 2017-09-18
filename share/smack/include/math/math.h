// This file is distributed under the MIT License. See LICENSE for details.
//

#ifndef MATH_H
#define MATH_H

//floats
float fabsf(float x);
float fdimf(float x, float y);
float roundf(float x);
//The following 3 functions are incomplete pending rounding mode implementation
float rintf(float x);
float nearbyintf(float x);
long lrintf(float x);
long lroundf(float x);
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
int __isnormalf(float x);
int __isSubnormalf(float x);
int __iszerof(float x);
int __isinff(float x);
int __isnanf(float x);
int __isnegativef(float x);
int __ispositivef(float x);
int __signbitf(float x);
int signbitf(float x);
int __fpclassifyf(float x);
int fpclassifyf(float x);
int __finitef(float x);
//float nan(float x);

//doubles
double fabs(double x);
double fdim(double x, double y);
double round(double x);
long lround(double x);
//The following 3 functions are incomplete pending rounding mode implementation
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
int __isSubnormal(double x);
int __iszero(double x);
int __isinf(double x);
int __isnan(double x);
int __isnegative(double x);
int __ispositive(double x);
int __signbit(double x);
int signbit(double x);
int __fpclassify(double x);
int fpclassify(double x);
int __finite(double x);

//long doubles
/*int __isnormall(long double x);
int __isSubnormall(long double x);
int __iszerol(long double x);
int __isinfl(long double x);
int __isnanl(long double x);
int __isnegativel(long double x);
int __ispositivel(long double x);
int __signbitl(long double x);
int signbitl(long double x);
int __fpclassifyl(long double x);
int fpclassifyl(long double x);
int __finitel(long double x);*/

#endif

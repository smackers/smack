#include "smack.h"

#if FLOAT_ENABLED && BIT_PRECISE
float __SMACK_convert_from_fp16_f32(unsigned short x) {
  float ret = __VERIFIER_nondet_float();
  __SMACK_code("@f := $fpext.bvhalf.bvfloat($rmode, $bitcast.bv16.bvhalf(@H));", ret, x);
  return ret;
}

double __SMACK_convert_from_fp16_f64(unsigned short x) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := $fpext.bvhalf.bvdouble($rmode, $bitcast.bv16.bvhalf(@H));", ret, x);
  return ret;
}

unsigned short __SMACK_convert_to_fp16_f32(float x) {
  unsigned short ret = __VERIFIER_nondet_unsigned_short();
  __SMACK_code("assume($bitcast.bv16.bvhalf(@H) == $fptrunc.bvfloat.bvhalf($rmode, @f));", ret, x);
  return ret;
}

unsigned short __SMACK_convert_to_fp16_f64(double x) {
  unsigned short ret = __VERIFIER_nondet_unsigned_short();
  __SMACK_code("assume $bitcast.bv16.bvhalf(@H) == $fptrunc.bvdouble.bvhalf($rmode, @);", ret, x);
  return ret;
}
#else
float __SMACK_convert_from_fp16_f32(unsigned short x) {
  return __VERIFIER_nondet_float();
}

double __SMACK_convert_from_fp16_f64(unsigned short x) {
  return __VERIFIER_nondet_double();
}

unsigned short __SMACK_convert_to_fp16_f32(float x) {
  return __VERIFIER_nondet_unsigned_short();
}

unsigned short __SMACK_convert_to_fp16_f64(double x) {
  return __VERIFIER_nondet_unsigned_short();
}
#endif

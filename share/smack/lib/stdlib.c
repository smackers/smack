//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include <stdlib.h>
#include <string.h>
#include <smack.h>

void* calloc(size_t num, size_t size) {
  void* ret;
  if (__VERIFIER_nondet_int()) {
    ret = 0;
  } else {
    ret = malloc(num * size);
    memset(ret, 0, num * size);
  }
  return ret;
}

void *realloc(void *ptr, size_t size) {
  free(ptr);
  return malloc(size);
}

long int strtol(const char *nptr, char **endptr, int base) {
  if (endptr != 0) {
    size_t size = strlen(nptr);
    unsigned nondet = __VERIFIER_nondet_unsigned_int();
    __VERIFIER_assume(nondet <= size);
    *endptr = (char *)nptr + nondet;
  }
  return __VERIFIER_nondet_long();
}

unsigned long int strtoul(const char *nptr, char **endptr, int base) {
  if (endptr != 0) {
    size_t size = strlen(nptr);
    unsigned nondet = __VERIFIER_nondet_unsigned_int();
    __VERIFIER_assume(nondet <= size);
    *endptr = (char *)nptr + nondet;
  }
  return __VERIFIER_nondet_unsigned_long();
}

unsigned long long int strtoull(const char *nptr, char **endptr, int base) {
  if (endptr != 0) {
    size_t size = strlen(nptr);
    unsigned nondet = __VERIFIER_nondet_unsigned_int();
    __VERIFIER_assume(nondet <= size);
    *endptr = (char *)nptr + nondet;
  }
  return __VERIFIER_nondet_unsigned_long_long();
}

double strtod(const char *nptr, char **endptr) {
  if (endptr != 0) {
    size_t size = strlen(nptr);
    unsigned nondet = __VERIFIER_nondet_unsigned_int();
    __VERIFIER_assume(nondet <= size);
    *endptr = (char *)nptr + nondet;
  }
  return __VERIFIER_nondet_double();
}

char *env_value_str = "xx";
char *getenv(const char *name) {
  if (__VERIFIER_nondet_int()) {
    return 0;
  } else {
    env_value_str[0] = __VERIFIER_nondet_char();
    env_value_str[1] = __VERIFIER_nondet_char();
    return env_value_str;
  }
}


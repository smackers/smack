// This file is distributed under the MIT License. See LICENSE for details.
//

#include <string.h>
#include <stdlib.h>

char *strcpy(char *dest, const char *src) {
  char *save = dest;
  while (*dest++ = *src++);
  return save;
}

size_t strlen(const char *str) {
  size_t count = 0;
  while (str[count] != 0) count++;
  return count;
}

char *strrchr(const char *src, int c) {
  char *result = (char *)0;

  while (*src != 0) {
    if (*src == c) {
      result = src;
    }
    src++;
  }
  return result;
}

size_t strspn(const char *cs, const char *ct) {
  size_t n;
  const char *p;
  for (n = 0; *cs; cs++, n++) {
    for (p = ct; *p && *p != *cs; p++);
    if (!*p) break;
  }
  return n;
}

unsigned long int strtoul(const char *nptr, char **endptr, int base) {
  if (__VERIFIER_nondet_int()) {
    if (endptr != 0) {
      *endptr = nptr;
    }
    return 0;
  } else {
    if (endptr != 0) {
      size_t size = strlen(nptr);
      *endptr = nptr + size;
    }
    return __VERIFIER_nondet_ulong();
  }
}

double strtod(const char *nptr, char **endptr) {
  if (__VERIFIER_nondet_int()) {
    if (endptr != 0) {
      *endptr = nptr;
    }
    return 0.0;
  } else {
    if (endptr != 0) {
      size_t size = strlen(nptr);
      *endptr = nptr + size;
    }
    return __VERIFIER_nondet_long();
  }
}

char *error_str = "xx";
char *strerror(int errnum) {
  error_str[0] = __VERIFIER_nondet_char();
  error_str[1] = __VERIFIER_nondet_char();
  return error_str;
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

void *realloc (void *__ptr, size_t __size) {
  free(__ptr);
  return malloc(__size);
}

//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include <string.h>
#include <stdlib.h>
#include <smack.h>

char *strcpy(char *dest, const char *src) {
  char *save = dest;
  while ((*dest++ = *src++));
  return save;
}

char *strncpy(char *dest, const char *src, size_t n) {
  size_t i;

  for (i = 0; i < n && src[i] != '\0'; i++)
    dest[i] = src[i];
  for ( ; i < n; i++)
    dest[i] = '\0';

  return dest;
}

size_t strlen(const char *str) {
  size_t count = 0;
  while (str[count]) count++;
  return count;
}

// comparison

int strcmp(const char *s1, const char *s2) {
  size_t n;
  for (n = 0; s1[n] == s2[n]; n++)
    if (s1[n] == '\0')
      return 0;
  return s1[n] - s2[n];
}

int strncmp(const char *s1, const char *s2, size_t n) {
  while (n--) {
    if (*s1 != *s2)
      return *s1 - *s2;
    s1++; 
    s2++;
  }
  
  return 0;
}

// concatenation

char *strcat(char *dest, const char *src) {
  char *retDest = dest;

  while (*dest)
    dest++;
  while ((*dest++ = *src++)) ;

  return retDest;
}

char *strncat(char *dest, const char *src, size_t n) {
  char *retDest = dest;

  while (*dest)
    dest++;
  while (n--) 
    *dest++ = *src++;
  *dest = '\0'; 

  return retDest;
}

// searching

char *strchr(const char *src, int c) {
  while (*src != 0) {
    if (*src == c) {
      return (char *)src;
    }
    src++;
  }

  return (char *)0;
}

char *strrchr(const char *src, int c) {
  char *result = (char *)0;

  while (*src != 0) {
    if (*src == c) {
      result = (char *)src;
    }
    src++;
  }
  return result;
}

size_t strspn(const char *s1, const char *s2) {
  size_t n;
  const char *p;
  for (n = 0; *s1; s1++, n++) {
    for (p = s2; *p && *p != *s1; p++);
    if (!*p) break;
  }
  return n;
}

size_t strcspn(const char *s1, const char *s2) {
  size_t n;
  const char *p;
  for (n = 0; *s1; s1++, n++) {
    for (p = s2; *p && *p != *s1; p++);
    if (*p) break;
  }
  return n;
}

char *strpbrk(const char *s1, const char *s2) {
  for (char *c1 = (char *)s1; *c1; c1++)
    for (char *c2 = (char *)s2; *c2; c2++)
      if (*c1 == *c2)
        return c1;
  return 0;
}

char *strstr(const char *haystack, const char *needle) {
  for (; *haystack; haystack++) {
    const char *h, *n;
    for (h = haystack, n = needle; *h && *n && (*h == *n); h++, n++);
    if (*n == '\0')
      return (char *)haystack;
  }
  return 0;
}

static char *olds;

char *strtok(char *str, const char *delim) {
  if (!str)
    str = olds;

  // if str and olds are empty, return 0
  if (!str)
    return 0;

  // skip first delims
  str += strspn(str,delim);
  if (*str == '\0')
    return 0;

  char *tok = str;
  // find end of token
  str = strpbrk(str,delim);
  if (!str) // this token finishes the string
    olds = 0;
  else {
    *str = '\0';
    olds = str + 1;
  }
  return tok;
}

char *error_str = "xx";
char *strerror(int errnum) {
  error_str[0] = __VERIFIER_nondet_char();
  error_str[1] = __VERIFIER_nondet_char();
  return error_str;
}


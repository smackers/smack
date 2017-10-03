// This file is distributed under the MIT License. See LICENSE for details.
//

#ifndef STRING_H
#define STRING_H

#include <stddef.h>

char *strcpy(char *dest, const char *src);
size_t strlen(const char *str);
char *strrchr(const char *src, int c);
size_t strspn(const char *cs, const char *ct);
unsigned long int strtoul(const char *nptr, char **endptr, int base);
double strtod(const char *nptr, char **endptr);
char *strerror(int errnum);
char *getenv(const char *name);
void *realloc (void *__ptr, size_t __size);

#endif

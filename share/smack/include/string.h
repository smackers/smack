//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef STRING_H
#define STRING_H

#include <stddef.h>

void *memcpy(void *str1, const void *str2, size_t n);
int memcmp(const void *str1, const void *str2, size_t n);
void *memset(void *str, int c, size_t n);

char *strcpy(char *dest, const char *src);
char *strncpy(char *dest, const char *src, size_t n);
size_t strlen(const char *str);
int strcmp(const char *s1, const char *s2);
int strncmp(const char *s1, const char *s2, size_t n);
char *strcat(char *dest, const char *src);
char *strncat(char *dest, const char *src, size_t n);
char *strchr(const char *src, int c);
char *strrchr(const char *src, int c);
size_t strspn(const char *s1, const char *s2);
size_t strcspn(const char *s1, const char *s2);
char *strpbrk(const char *s1, const char *s2);
char *strstr(const char *haystack, const char *needle);
char *strtok(char *str, const char *delim);
char *strerror(int errnum);

#endif

//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef SMACK_SVCOMP_H_
#define SMACK_SVCOMP_H_

#include "smack.h"

#define __inline // Remove the inline attribute
#define __builtin_expect __builtinx_expect // Rewrite so that clang does not complain
#define __builtin_memcpy __builtinx_memcpy // Rewrite so that clang does not complain
#define __builtin_va_start __builtinx_va_start // Rewrite so that clang does not complain
#define __builtin_object_size __builtinx_object_size // Rewrite so that clang does not complain

void __VERIFIER_error(void);
void __VERIFIER_assume(int);
void exit(int);


// Types to be overloaded for: {bool, float, loff_t, pchar,
// pthread_t, sector_t, size_t, u32}

char __VERIFIER_nondet_char(void);
short __VERIFIER_nondet_short(void);
int __VERIFIER_nondet_int(void);
long __VERIFIER_nondet_long(void);
unsigned char __VERIFIER_nondet_uchar(void);
unsigned short __VERIFIER_nondet_ushort(void);
unsigned __VERIFIER_nondet_uint(void);
unsigned long __VERIFIER_nondet_ulong(void);
void* __VERIFIER_nondet_pointer(void);

#endif


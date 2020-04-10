//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef SMACK_H_
#define SMACK_H_
#include <limits.h>

/**
 * The SMACK "prelude" declarations
 */

#ifdef __cplusplus
extern "C" {
#endif

#ifdef SVCOMP
// Apprently needed by SVCOMP benchmarks
#define __inline
#define __builtin_expect __builtinx_expect
#define __builtin_memcpy __builtinx_memcpy
#define __builtin_va_start __builtinx_va_start
#define __builtin_object_size __builtinx_object_size

// For handling of va_start macro
void __builtinx_va_start(char *, char *);
#endif

void __SMACK_code(const char *fmt, ...);
void __SMACK_mod(const char *fmt, ...);
void __SMACK_decl(const char *fmt, ...);
void __SMACK_top_decl(const char *fmt, ...);

typedef struct smack_value {
  void *dummy;
} * smack_value_t;
smack_value_t __SMACK_value();
smack_value_t __SMACK_values(void *ary, unsigned count);
smack_value_t __SMACK_return_value(void);

// Sugar for __SMACK_init_func_XXX()
#define __SMACK_INIT(x) void __SMACK_init_func_##x()

#if MEMORY_SAFETY
// Inserts memory access checks in form of assert to check null pointer access
// and buffer overflow errors
void __SMACK_check_memory_safety(void *, void *) __attribute__((const));
void __SMACK_check_memory_leak(void);
#endif

// We need this to enforce that assert/assume are function calls
// with an integer argument (DSA gets confused otherwise)
__attribute__((always_inline)) void __SMACK_dummy(int v);

void __VERIFIER_assume(int);
#ifndef CUSTOM_VERIFIER_ASSERT
void __VERIFIER_assert(int);
#endif
void __VERIFIER_error(void);

#ifndef AVOID_NAME_CONFLICTS
#define assert(EX)                                                             \
  do {                                                                         \
    if (!(EX))                                                                 \
      __VERIFIER_assert(0);                                                    \
  } while (0)
#define assume(EX)                                                             \
  do {                                                                         \
    if (!(EX))                                                                 \
      __VERIFIER_assume(0);                                                    \
  } while (0)
#endif

#define S4(a, b, c, d) a b c d
#define S3(a, b, c) a b c
#define S2(a, b) a b
#define S1(a) a
#define U4(a, b, c, d) a##_##b##_##c##_##d
#define U3(a, b, c) a##_##b##_##c
#define U2(a, b) a##_##b
#define U1(a) a

#define TY(_1, _2, _3, _4, A, ...) A

#define S(...) TY(__VA_ARGS__, S4, S3, S2, S1)(__VA_ARGS__)
#define U(...) TY(__VA_ARGS__, U4, U3, U2, U1)(__VA_ARGS__)

#define NONDET_DECL(P, ty...) S(ty) U(P, U(ty))(void)

void *__VERIFIER_nondet(void);
NONDET_DECL(__SMACK_nondet, char);
NONDET_DECL(__SMACK_nondet, signed, char);
NONDET_DECL(__SMACK_nondet, unsigned, char);
NONDET_DECL(__SMACK_nondet, short);
NONDET_DECL(__SMACK_nondet, short, int);
NONDET_DECL(__SMACK_nondet, signed, short);
NONDET_DECL(__SMACK_nondet, signed, short, int);
NONDET_DECL(__SMACK_nondet, unsigned, short);
NONDET_DECL(__SMACK_nondet, unsigned, short, int);
NONDET_DECL(__SMACK_nondet, int);
NONDET_DECL(__SMACK_nondet, signed, int);
NONDET_DECL(__SMACK_nondet, unsigned);
NONDET_DECL(__SMACK_nondet, unsigned, int);
NONDET_DECL(__SMACK_nondet, long);
NONDET_DECL(__SMACK_nondet, long, int);
NONDET_DECL(__SMACK_nondet, signed, long);
NONDET_DECL(__SMACK_nondet, signed, long, int);
NONDET_DECL(__SMACK_nondet, unsigned, long);
NONDET_DECL(__SMACK_nondet, unsigned, long, int);
NONDET_DECL(__SMACK_nondet, long, long);
NONDET_DECL(__SMACK_nondet, long, long, int);
NONDET_DECL(__SMACK_nondet, signed, long, long);
NONDET_DECL(__SMACK_nondet, signed, long, long, int);
NONDET_DECL(__SMACK_nondet, unsigned, long, long);
NONDET_DECL(__SMACK_nondet, unsigned, long, long, int);
NONDET_DECL(__VERIFIER_nondet, char);
NONDET_DECL(__VERIFIER_nondet, signed, char);
NONDET_DECL(__VERIFIER_nondet, unsigned, char);
NONDET_DECL(__VERIFIER_nondet, short);
NONDET_DECL(__VERIFIER_nondet, short, int);
NONDET_DECL(__VERIFIER_nondet, signed, short);
NONDET_DECL(__VERIFIER_nondet, signed, short, int);
NONDET_DECL(__VERIFIER_nondet, unsigned, short);
NONDET_DECL(__VERIFIER_nondet, unsigned, short, int);
NONDET_DECL(__VERIFIER_nondet, int);
NONDET_DECL(__VERIFIER_nondet, signed, int);
NONDET_DECL(__VERIFIER_nondet, unsigned);
NONDET_DECL(__VERIFIER_nondet, unsigned, int);
NONDET_DECL(__VERIFIER_nondet, long);
NONDET_DECL(__VERIFIER_nondet, long, int);
NONDET_DECL(__VERIFIER_nondet, signed, long);
NONDET_DECL(__VERIFIER_nondet, signed, long, int);
NONDET_DECL(__VERIFIER_nondet, unsigned, long);
NONDET_DECL(__VERIFIER_nondet, unsigned, long, int);
NONDET_DECL(__VERIFIER_nondet, long, long);
NONDET_DECL(__VERIFIER_nondet, long, long, int);
NONDET_DECL(__VERIFIER_nondet, signed, long, long);
NONDET_DECL(__VERIFIER_nondet, signed, long, long, int);
NONDET_DECL(__VERIFIER_nondet, unsigned, long, long);
NONDET_DECL(__VERIFIER_nondet, unsigned, long, long, int);
NONDET_DECL(__VERIFIER_nondet, float);
NONDET_DECL(__VERIFIER_nondet, double);
NONDET_DECL(__VERIFIER_nondet, long, double);

#undef S1
#undef S2
#undef S3
#undef S4
#undef U1
#undef U2
#undef U3
#undef U4
#undef TY
#undef S
#undef U
#undef NONDET_DECL

// Used in SVCOMP benchmarks
#ifdef __cplusplus
bool __VERIFIER_nondet_bool(void);
#else
_Bool __VERIFIER_nondet_bool(void);
#endif
unsigned char __VERIFIER_nondet_uchar(void);
unsigned short __VERIFIER_nondet_ushort(void);
unsigned __VERIFIER_nondet_uint(void);
unsigned long __VERIFIER_nondet_ulong(void);
void *__VERIFIER_nondet_pointer(void);

void __SMACK_decls(void);

// Concurrency helper functions
void __VERIFIER_atomic_begin();
void __VERIFIER_atomic_end();

#ifdef __cplusplus
}
#endif

#endif /*SMACK_H_*/

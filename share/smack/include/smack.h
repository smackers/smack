//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef SMACK_H_
#define SMACK_H_

/**
 * The SMACK "prelude" declarations
 */

#ifdef __cplusplus
extern "C" {
#endif

// Apprently needed by SVCOMP benchmarks
#define __inline
#define __builtin_expect __builtinx_expect
#define __builtin_memcpy __builtinx_memcpy
#define __builtin_va_start __builtinx_va_start
#define __builtin_object_size __builtinx_object_size

// For handling of va_start macro
void __builtinx_va_start(char*,char*);

void __SMACK_code(const char *fmt, ...);
void __SMACK_mod(const char *fmt, ...);
void __SMACK_decl(const char *fmt, ...);
void __SMACK_top_decl(const char *fmt, ...);

typedef struct smack_value { void* dummy; }* smack_value_t;
smack_value_t __SMACK_value();
smack_value_t __SMACK_values(void* ary, unsigned count);
smack_value_t __SMACK_return_value(void);

// Sugar for __SMACK_init_func_XXX()
#define __SMACK_INIT(x) void __SMACK_init_func_##x()

// Inserts memory access checks in form of assert to check null pointer access
// and buffer overflow errors
void __SMACK_check_memory_safety(void*, unsigned long);

// We need this to enforce that assert/assume are function calls
// with an integer argument (DSA gets confused otherwise)
__attribute__((always_inline)) void __SMACK_dummy(int v);

void __VERIFIER_assume(int);
#ifndef CUSTOM_VERIFIER_ASSERT
void __VERIFIER_assert(int);
#endif
void __VERIFIER_error(void);
void exit(int);

#ifndef AVOID_NAME_CONFLICTS
#define assert(EX) __VERIFIER_assert(EX)
#define assume(EX) __VERIFIER_assume(EX)
#endif

#define S4(a,b,c,d) a b c d
#define S3(a,b,c) a b c
#define S2(a,b) a b
#define S1(a) a
#define U4(a,b,c,d) a ## _ ## b ## _ ## c ## _ ## d
#define U3(a,b,c) a ## _ ## b ## _ ## c
#define U2(a,b) a ## _ ## b
#define U1(a) a

#define TY(_1, _2, _3, _4, A, ...) A

#define S(...) TY(__VA_ARGS__, S4, S3, S2, S1)(__VA_ARGS__)
#define U(...) TY(__VA_ARGS__, U4, U3, U2, U1)(__VA_ARGS__)

#define NONDET_DECL(ty...) S(ty) U(__VERIFIER_nondet,U(ty)) ()

void* __VERIFIER_nondet(void);
NONDET_DECL(char);
NONDET_DECL(signed,char);
NONDET_DECL(unsigned,char);
NONDET_DECL(short);
NONDET_DECL(short,int);
NONDET_DECL(signed,short);
NONDET_DECL(signed,short,int);
NONDET_DECL(unsigned,short);
NONDET_DECL(unsigned,short,int);
NONDET_DECL(int);
NONDET_DECL(signed,int);
NONDET_DECL(unsigned);
NONDET_DECL(unsigned,int);
NONDET_DECL(long);
NONDET_DECL(long,int);
NONDET_DECL(signed,long);
NONDET_DECL(signed,long,int);
NONDET_DECL(unsigned,long);
NONDET_DECL(unsigned,long,int);
NONDET_DECL(long,long);
NONDET_DECL(long,long,int);
NONDET_DECL(signed,long,long);
NONDET_DECL(signed,long,long,int);
NONDET_DECL(unsigned,long,long);
NONDET_DECL(unsigned,long,long,int);
NONDET_DECL(float);
NONDET_DECL(double);
NONDET_DECL(long,double);

// Apparently used in SVCOMP benchmarks
_Bool __VERIFIER_nondet_bool(void);
unsigned char __VERIFIER_nondet_uchar(void);
unsigned short __VERIFIER_nondet_ushort(void);
unsigned __VERIFIER_nondet_uint(void);
unsigned long __VERIFIER_nondet_ulong(void);
void* __VERIFIER_nondet_pointer(void);

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

void __SMACK_decls();

#ifdef __cplusplus
}
#endif

#endif /*SMACK_H_*/

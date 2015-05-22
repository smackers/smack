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

void __SMACK_code(const char *fmt, ...);
void __SMACK_mod(const char *fmt, ...);
void __SMACK_decl(const char *fmt, ...);
void __SMACK_top_decl(const char *fmt, ...);

// Sugar for __SMACK_init_func_XXX()
#define __SMACK_INIT(x) void __SMACK_init_func_##x()

// We need this to enforce that assert/assume are function calls
// with an integer argument (DSA gets confused otherwise)
__attribute__((always_inline)) void __SMACK_dummy(int v);

#define __VERIFIER_assert(EX) do { __SMACK_dummy(EX); __SMACK_code("assert @ != $0;", EX); } while (0)
#define __VERIFIER_assume(EX) do { __SMACK_dummy(EX); __SMACK_code("assume @ != $0;", EX); } while (0)

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


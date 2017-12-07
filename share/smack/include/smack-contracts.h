//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef SMACK_CONTRACTS_H_
#define SMACK_CONTRACTS_H_

#include <stdbool.h>

void __CONTRACT_requires(bool expr);
void __CONTRACT_ensures(bool expr);
void __CONTRACT_invariant(bool expr);

#define requires(X) __CONTRACT_requires(X)
#define ensures(X) __CONTRACT_ensures(X)
#define invariant(X) __CONTRACT_invariant(X)

// TODO provide quantifier bound variables
// int  __CONTRACT_int_variable(const char *name) __attribute__((const));
// #define qvar(X,T) __CONTRACT_ ## T ## _variable(X)

// TODO provide universal quantifier
// bool __CONTRACT_forall(const char *var, bool expr) __attribute__((const));
// #define forall(X,Y) __CONTRACT_forall(X,Y)

// TODO provide existential quantifier
// bool __CONTRACT_exists(const char *var, bool expr) __attribute__((const));
// #define exists(X,Y) __CONTRACT_exists(X,Y)

// TODO provide precondition state “old” expressions
// int old(int term);

// TODO provide procedure “result” expression
// int result(void);

#endif

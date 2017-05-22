//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef SMACK_CONTRACTS_H_
#define SMACK_CONTRACTS_H_

#include <stdbool.h>

void __CONTRACT_requires(bool expr);
void __CONTRACT_ensures(bool expr);
void __CONTRACT_invariant(bool expr);
int  __CONTRACT_int_variable(const char *name) __attribute__((const));
bool __CONTRACT_forall(const char *var, bool expr) __attribute__((const));
bool __CONTRACT_exists(const char *var, bool expr) __attribute__((const));

#define requires(X) __CONTRACT_requires(X)
#define ensures(X) __CONTRACT_ensures(X)
#define invariant(X) __CONTRACT_invariant(X)
#define qvar(X,T) __CONTRACT_ ## T ## _variable(X)
#define forall(X,Y) __CONTRACT_forall(X,Y)
#define exists(X,Y) __CONTRACT_exists(X,Y)

int old(int term);
int result(void);

#endif

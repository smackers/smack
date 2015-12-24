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

bool forall(const char *var, bool expr);
bool exists(const char *var, bool expr);
int qvar(const char *var);
int old(int term);
int result(void);

#undef bool
#undef true
#undef false

#endif

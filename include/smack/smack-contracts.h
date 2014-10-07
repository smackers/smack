//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef SMACK_CONTRACTS_H_
#define SMACK_CONTRACTS_H_

#include <stdbool.h>

void requires(bool expr);
void ensures(bool expr);
void invariant(bool expr);

bool forall(const char *var, bool expr);
bool exists(const char *var, bool expr);
int qvar(const char *var);
int old(int term);
int result(void);

#endif

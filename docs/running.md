## Running SMACK


SMACK software verifier is run using the `smack` tool in the bin directory.
For a given input C/C++ program, the tool checks for violations of user-provided
assertions. SMACK has a number of command line options that can be used
to fine-tune the toolchain. Type `smack -h` for a full list of supported command
line options.


### Using The SMACK Verifier

Next, we illustrate how to verify the following simple C program using the SMACK
verifier:
```C
// examples/simple/simple.c
#include "smack.h"
#include <stdlib.h>

#define TRUE 1
#define FALSE 0
#define MAX_LIMIT 1000

// Bank Account Example

// Account structure
typedef struct {
  int balance;
  int limit;
} ACCOUNT, *PACCOUNT;

// Create and initialize account
PACCOUNT create(int limit) {
  if (limit <= 0 || limit > MAX_LIMIT) return 0;
  PACCOUNT acc = (PACCOUNT) malloc(sizeof(ACCOUNT));
  acc->balance = 0;
  acc->limit = limit;
  return acc;
}

// Get account balance
int get_balance(PACCOUNT acc) {
  return acc->balance;
}

// Deposit funds if not exceeding the account limit
int deposit(PACCOUNT acc, int n) {
  if (n <= 0) return FALSE;
  if (acc->balance > acc->limit - n) {
    return FALSE;
  }
  acc->balance = acc->balance + n;
  return TRUE;
}

// Withdraw if there is enough funds in the account
int withdraw(PACCOUNT acc, int n) {
  if (n <= 0) return FALSE;
  if (acc->balance >= n) {
    acc->balance = acc->balance - n;
    return TRUE;
  }
  return FALSE;
}

// Simple unit test for account
void test_account(int x, int y, int z) {
  PACCOUNT acc;
  int ops = 0;

  acc = create(x);
  if (!acc) {
    assert(x <= 0 || x > MAX_LIMIT);
    return;
  }
  ops += deposit(acc, y);
  assert(get_balance(acc) >=0 && get_balance(acc) <= MAX_LIMIT);
  ops += deposit(acc, z);
  assert(get_balance(acc) >=0 && get_balance(acc) <= MAX_LIMIT);
  ops += withdraw(acc, z);
  assert(get_balance(acc) >=0 && get_balance(acc) <= MAX_LIMIT);
  assert(ops < 3 || get_balance(acc) == y);
  free(acc);
  return;
}

int main(void) {
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  int z = __VERIFIER_nondet_int();

  // Check account with nondeterministic values
  test_account(x, y, z);
  return 0;
}
```
Note that this example can also be found in the smack/examples/simple
directory. SMACK defines a number of functions (one for each basic type)
for introducing nondeterministic (i.e., unconstrained) values, such as
`__VERIFIER_nondet_int` used in this example.

Simply run the SMACK verifier on your input C file:
```Shell
smack simple.c
```
SMACK should report no errors for this example.

Under the hood, SMACK first compiles the example into an LLVM bitcode file using Clang:
```Shell
clang -c -Wall -emit-llvm -O0 -g -Xclang -disable-O0-optnone -I../../share/smack/include simple.c -o simple.bc
```
We use the `-g` flag to compile with debug information enabled, which the SMACK
verifier leverages to generate more informative error traces. Then, the generated bitcode
file is translated into Boogie code, which is in turn passed to the chosen back-end
verifier.

For mode advanced usage scenarios, please refer to our [usage notes](usage-notes.md).


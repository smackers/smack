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

int incr(int x) {
  return x + 1;
}

int main(void) {
  int a, b;

  a = b = __VERIFIER_nondet_int();
  a = incr(a);
  assert(a == b + 1);
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
clang -c -Wall -emit-llvm -O0 -g -I../../share/smack/include simple.c -o simple.bc
```
We use the `-g` flag to compile with debug information enabled, which the SMACK
verifier leverages to generate more informative error traces. Then, the generated bitcode
file is translated into Boogie code, which is in turn passed to the chosen back-end
verifier.


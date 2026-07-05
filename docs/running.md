## Running SMACK


SMACK software verifier is run using the `smack` tool in the bin directory.
For a given input C/C++ program, the tool checks for violations of user-provided
assertions, as well as automatically generated assertions for built-in property
checks such as memory safety and integer overflow (see [Checking Memory
Safety](#checking-memory-safety) and [Checking Integer
Overflow](#checking-integer-overflow) below). SMACK has a number of command line
options that can be used to fine-tune the toolchain. Type `smack -h` for a full
list of supported command line options.


### Using The SMACK Verifier

Next, we illustrate how to verify the following simple C program using the SMACK
verifier:
```C
// examples/simple/simple.c
#include "smack.h"
#include <assert.h>
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
Note that this example can also be found in the `examples/simple` directory. It
uses the three building blocks that SMACK programs rely on to express
verification problems:

- **`__VERIFIER_nondet_<type>()`** returns an unconstrained (i.e.,
  *nondeterministic*) value of the given type. SMACK reasons about *all*
  possible return values simultaneously, so these functions are used to model
  arbitrary or unknown inputs. SMACK defines one such function for each basic
  type, e.g., `__VERIFIER_nondet_int` (used above) and
  `__VERIFIER_nondet_unsigned_long`. They are declared in `smack.h`.
- **`assert(cond)`** states a property that must hold on every execution. If
  SMACK finds any execution that reaches the assertion with `cond` evaluating to
  false, it reports an error along with a counterexample trace; otherwise the
  assertion is verified. `assert` is the standard C macro: SMACK ships its own
  `<assert.h>` (and `<cassert>` for C++) that connects it to the verifier, so
  **you must `#include <assert.h>`** for your assertions to be checked. If you
  forget it, Clang emits an *implicit declaration of function 'assert'* warning
  and the assertions are silently ignored.
- **`assume(cond)`** restricts verification to the executions in which `cond`
  holds. It is typically used to constrain nondeterministic inputs — for
  example, `assume(x > 0)` discards every execution in which `x <= 0`. `assume`
  is provided by `smack.h`.

Simply run the SMACK verifier on your input C file:
```Shell
smack simple.c
```
SMACK should report no errors for this example:
```
SMACK found no errors with unroll bound 1.
```

Under the hood, SMACK first compiles the example into an LLVM bitcode file using Clang:
```Shell
clang -c -Wall -emit-llvm -O0 -g -Xclang -disable-O0-optnone -I../../share/smack/include simple.c -o simple.bc
```
We use the `-g` flag to compile with debug information enabled, which the SMACK
verifier leverages to generate more informative error traces. Then, the generated bitcode
file is translated into Boogie code, which is in turn passed to the chosen back-end
verifier.

### Understanding SMACK's Output

When SMACK finishes, it reports one of two outcomes.

If no assertion — user-written or automatically generated — can be violated
within the current bounds, SMACK reports success:
```
SMACK found no errors with unroll bound 1.
```
Recall that SMACK is a *bounded* verifier: by default it unrolls loops and
recursion only once (`--unroll 1`). "No errors with unroll bound `N`" therefore
means the program is safe along every execution that stays within that bound; a
bug that only manifests after more iterations may be missed. Increase the bound
with `--unroll N` to explore deeper (the [usage notes](usage-notes.md) discuss
how to choose a bound).

If an assertion can be violated, SMACK reports an error together with a
counterexample trace. The following program asserts a property that does not hold
for every allowed input:
```C
// buggy.c
#include "smack.h"
#include <assert.h>

int main(void) {
  int x = __VERIFIER_nondet_int();
  assume(x >= 5);
  assert(x >= 10); // fails, e.g., when x == 5
  return 0;
}
```
```Shell
smack buggy.c
```
```
buggy.c(5,11): CALL __VERIFIER_nondet_int
...
buggy.c(5,11): RETURN from __VERIFIER_nondet_int, ... x = 8
buggy.c(7,3): CALL __VERIFIER_assert
...
SMACK found an error.
```
The trace lists the steps of a concrete execution that reaches the failing
assertion, annotated with source locations (`file(line,column)`) and the values
of variables along the way. Here it exhibits `x = 8`, which satisfies
`assume(x >= 5)` but violates `assert(x >= 10)`, as a counterexample. The `-g`
debug information that SMACK compiles with is what makes these source-level
traces possible.

### Checking Memory Safety

Beyond user-written assertions, SMACK can automatically check that a program is
*memory safe*. When memory-safety checking is enabled, SMACK instruments the
program with generated assertions that guard every memory access and
deallocation, so no assertions need to be written by hand. The `memory-safety`
property is the union of three sub-properties, each of which can also be checked
on its own:

- `valid-deref` — every pointer dereference targets a live, in-bounds object
- `valid-free` — every `free` releases a heap object exactly once
- `memleak` — every allocated object is eventually freed

Consider the following program, which reads one element past the end of a
ten-element array:
```C
// memsafe.c
#include "smack.h"
#include <stdlib.h>

int main(void) {
  int *a = malloc(10 * sizeof(int));
  int x = a[10]; // out-of-bounds read: valid indices are 0..9
  free(a);
  return x;
}
```
Running SMACK with the `--check memory-safety` option detects the buffer
overflow:
```Shell
smack memsafe.c --check memory-safety
```
```
SMACK found an error: invalid pointer dereference.
```
Pass `--check valid-deref`, `--check valid-free`, or `--check memleak` instead to
check an individual sub-property.

### Checking Integer Overflow

SMACK can also check for signed integer overflow, which is undefined behavior in
C. With the `--check integer-overflow` option, SMACK inserts a generated
assertion before each arithmetic operation that could overflow, verifying that
the result stays within the range of its type.

The following program adds two nondeterministic integers, whose sum may exceed
the maximum value representable by an `int`:
```C
// overflow.c
#include "smack.h"

int main(void) {
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  return x + y; // may overflow the range of int
}
```
```Shell
smack overflow.c --check integer-overflow
```
SMACK finds inputs that trigger the overflow and prints a trace leading to it:
```
overflow.c(4,11): ... x = 2147482411
overflow.c(5,11): ... y = 1237
SMACK found an error: integer overflow.
```
By default every function is checked; use `--checked-functions` to restrict
property checking to a specific set of functions, for example
`--checked-functions main compute`.

### Verifying Programs That Span Multiple Files

Real-world programs are usually split across several source files. SMACK accepts
multiple input files on the command line, compiling each one and linking the
resulting LLVM bitcode into a single whole-program module before verification:
```Shell
smack simple.c incr.c
```
```
SMACK found no errors with unroll bound 1.
```
A complete two-file example is available in the `examples/simple-project`
directory.

For larger projects, you can instead produce a single whole-program LLVM bitcode
file yourself and hand that file to SMACK. Compile each translation unit to
bitcode with `clang -c -emit-llvm -g`, link the results together with
`llvm-link`, and run SMACK on the combined bitcode. The `Makefile` in the
`examples/simple-project` directory automates exactly these steps, producing a
`simple-project.bc` that you can verify directly:
```Shell
smack simple-project.bc
```

### Selecting a Verification Back-end and Solver

SMACK translates the input program into Boogie and then discharges it with a
back-end verification engine, selected with `--verifier`:

- **`corral`** (the default) is a bounded model checker that inlines procedures
  and unrolls loops up to the given bound. It is also the engine used for
  concurrent programs (see `--pthread` and `--context-bound` in the
  [usage notes](usage-notes.md)).
- **`boogie`** discharges verification conditions with an SMT solver. It is a
  useful alternative, in particular when experimenting with modular,
  contract-based verification.

For example, to verify the introductory program with Boogie instead of Corral:
```Shell
smack simple.c --verifier=boogie
```
Underneath either engine, an SMT solver decides the generated formulas. SMACK
uses Z3 by default and can also use CVC5 or Yices2 — each an optional dependency
that must be installed separately — selected with `--solver`:
```Shell
smack simple.c --solver=cvc5
```

Run `smack -h` for the complete list of command line options. For more advanced
usage scenarios, please refer to our [usage notes](usage-notes.md).


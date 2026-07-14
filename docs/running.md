## Running SMACK


SMACK software verifier is run using the `smack` tool in the bin directory.
For a given input C/C++ program, the tool checks selected properties. With no
`--check` option, the selected property set consists of user-provided
assertions. The `--check` option can instead select automatically generated
checks such as
memory safety and integer overflow, or select those checks together with
`assertions` (see [Checking Memory Safety](#checking-memory-safety) and
[Checking Integer Overflow](#checking-integer-overflow) below). SMACK has a
number of command-line options that can be used to fine-tune the toolchain. Type
`smack -h` for a full list of supported command-line options.


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
- **`assert(cond)`** states a property that must hold. If SMACK finds an
  execution in its verification model that reaches the assertion with `cond`
  evaluating to false, it reports an error along with a counterexample trace.
  Otherwise, no violation of that assertion was found under the selected model
  and bounds. `assert` is the standard C macro: SMACK ships its own `<assert.h>`
  (and `<cassert>` for C++) that connects it to the verifier, so **you must
  `#include <assert.h>`** for your assertions to be checked. If you forget it,
  Clang can emit an *implicit declaration of function 'assert'* warning in C
  and silently ignore the assertions; C++ normally rejects the undeclared
  identifier.
- **`assume(cond)`** restricts verification to the executions in which `cond`
  holds. It is typically used to constrain nondeterministic inputs — for
  example, `assume(x > 0)` discards every execution in which `x <= 0`. `assume`
  is provided by `smack.h`.

Simply run the SMACK verifier on your input C file:
```Shell
smack simple.c
```
Because this invocation does not specify `--check`, SMACK checks the program's
assertions. It should report no errors for this example:
```
SMACK found no errors with unroll bound 1.
```

Under the hood, SMACK first compiles the example into an LLVM bitcode file using
the Clang version from its configured LLVM toolchain (LLVM 14 for this release):
```Shell
clang-14 -c -Wall -emit-llvm -O0 -g -Xclang -disable-O0-optnone -I../../share/smack/include simple.c -o simple.bc
```
We use the `-g` flag to compile with debug information enabled, which the SMACK
verifier leverages to generate more informative error traces. Then, the generated bitcode
file is translated into Boogie code, which is in turn passed to the chosen back-end
verifier.

### Understanding SMACK's Output

When SMACK finishes, it reports one of four result kinds: it found no errors, it
found an error, it timed out, or the result is unknown. A timeout or unknown
result is inconclusive; neither establishes a property nor supplies a confirmed
counterexample.

If the back-end finds no violation of the selected properties in the generated
verification model within the current bounds, SMACK reports:
```
SMACK found no errors with unroll bound 1.
```
Recall that SMACK is a *bounded* verifier: by default it unrolls loops and
recursion only once (`--unroll 1`). "No errors with unroll bound `N`" therefore
means only that no error was found for the selected properties in SMACK's model
within that bound. It is not, by itself, a proof of safety for all C executions.
A bug that requires more iterations may be missed, and integer, floating-point,
external-library, or other approximations can make the verification model
differ from the C program. Increase the bound with `--unroll N` to explore
deeper (the [usage notes](usage-notes.md) discuss how to choose a bound), and
choose modeling options appropriate to the property being checked.

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
buggy.c(6,11): CALL __VERIFIER_nondet_int
...
buggy.c(6,11): RETURN from __VERIFIER_nondet_int, ... x = 8
buggy.c(8,3): CALL __VERIFIER_assert
...
SMACK found an error.
```
The trace describes a witness in SMACK's verification model, annotated with
source locations (`file(line,column)`) and model values along the way. Here it
exhibits `x = 8`, which satisfies `assume(x >= 5)` but violates
`assert(x >= 10)`. When the relevant operations are modeled precisely, such a
witness corresponds to a concrete source execution. Approximate integer,
floating-point, library, or other models can instead produce an abstract or
spurious counterexample, so validate suspicious traces against the selected
modeling options. The `-g` debug information that SMACK compiles with is what
makes these source-level traces possible.

### Checking Memory Safety

SMACK can automatically check that a program is *memory safe*. When
memory-safety checking is enabled, SMACK instruments the program with generated
assertions that guard every memory access and deallocation, so no assertions
need to be written by hand. The `memory-safety` property is the union of three
sub-properties, each of which can also be checked on its own:

- `valid-deref` — every pointer dereference targets a live, in-bounds object
- `valid-free` — every `free(p)` receives either `NULL` or the base address of a
  currently allocated heap object
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
An explicit `--check` list replaces the default `assertions` selection; it does
not add to it. The command above checks memory safety but would not check any
user-written assertions in `memsafe.c`. To check both, select both properties:

```Shell
smack memsafe.c --check assertions memory-safety
```

Pass `--check valid-deref`, `--check valid-free`, or `--check memleak` instead to
check only an individual sub-property. Include `assertions` in the same list if
user-written assertions should also be checked.

### Checking Integer Overflow

SMACK can also check for signed integer overflow, which is undefined behavior in
C. With the `--check integer-overflow` option, SMACK instruments checked signed
arithmetic and shift operations with generated assertions. These checks cover
arithmetic results outside the range of their type as well as invalid or
overflowing shifts.

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
overflow.c(5,11): ... x = 2147482411
overflow.c(6,11): ... y = 1237
SMACK found an error: integer overflow.
```
This command selects only integer-overflow checks. To check user-written
assertions at the same time, run:

```Shell
smack overflow.c --check assertions integer-overflow
```

By default every function is checked; use `--checked-functions` to restrict
property checking to a specific set of functions, for example
`--checked-functions main compute`. This restriction also suppresses
user-written assertions in functions whose names do not match.

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
file yourself and hand that file to SMACK. Compile each translation unit with
the Clang version that matches SMACK's configured LLVM toolchain and link the
results with the matching `llvm-link` (currently `clang-14` and
`llvm-link-14`). Manual compilation must also reproduce SMACK's frontend flags
for the selected properties. In particular, add
`-fsanitize=signed-integer-overflow,shift` when building bitcode for
`--check integer-overflow`; supplying that property only after the source has
already been compiled cannot add Clang's overflow instrumentation. See [Build
Workflows](build-workflows.md) for the complete commands. The `Makefile` in the
`examples/simple-project` directory demonstrates the basic multi-file pattern,
producing a `simple-project.bc` that you can verify directly:
```Shell
smack simple-project.bc --check assertions integer-overflow
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

Run `smack -h` for the complete command-line help. For explanations of the
options users most commonly need, including `--unroll`,
`--integer-encoding=bit-vector`, `--float`, and `--pthread`, see
[Command-Line Options](command-line-options.md). For larger programs, see
[Build Workflows](build-workflows.md). For custom models and inline Boogie, see
[Advanced Modeling](advanced.md). For common failure modes, see
[Troubleshooting](troubleshooting.md).

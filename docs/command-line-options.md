## Command-Line Options

This page explains the options users most often need, and why those options
exist. It is checked against the `smack` parser in `share/smack/top.py`. Run
`smack -h` for the complete authoritative help text.

The general form is:

```Shell
smack [options] input-files...
```

### `--check`: Select the Properties to Verify

With no `--check` option, SMACK checks user assertions. Supplying `--check`
replaces that default; it does not add properties alongside assertions. For
example, this checks integer overflow but not user assertions:

```Shell
smack file.c --check integer-overflow
```

List every property that you want checked. To retain assertion checking while
also checking memory safety or integer overflow, use:

```Shell
smack file.c --check assertions memory-safety
smack file.c --check assertions integer-overflow
```

`memory-safety` is shorthand for the `valid-deref`, `valid-free`, and `memleak`
properties.

### `--unroll`: Look Deeper Into Loops and Recursion

SMACK is bounded by default. It verifies loops and recursion only up to the
selected bound, which is `1` unless you say otherwise.

```C
#include "smack.h"
#include <assert.h>

int main(void) {
  int i = 0;
  while (i < 3) {
    i++;
  }
  assert(i != 3);
}
```

With the default bound, SMACK may not reach the failing assertion. Increase the
bound when the behavior you care about needs more iterations:

```Shell
smack loop.c --unroll 4
```

For this loop, the fourth visit to the loop header is needed to take the exit
after the three iterations. A bound of `3` still does not reach the assertion.

`--fail-on-loop-exit` inserts a failing assertion in each normal loop exit
block. A loop-exit report therefore says that a normal exit was reachable in
the selected model and bound:

```Shell
smack loop.c --unroll 4 --fail-on-loop-exit
```

This sample's user assertion is also reachable at bound `4`. To exercise only
the injected loop-exit check, remove the user assertion; a report naming
`__SMACK_loop_exit` is from the injected check.

This option does not report paths that the verifier cuts off when the unroll
bound is exhausted. It therefore cannot, by itself, show that a successful
result was independent of the bound.

If SMACK reports:

```text
SMACK found no errors with unroll bound 4.
```

that means no error was found in the selected translation and models within
that bound. It is not a proof for arbitrarily many iterations unless the
selected back-end and mode establish such a proof, and translation
approximations are separate from bounding. In particular, a counterexample
from an approximate integer, bitwise, or floating-point model need not be a
concrete C execution.

### `--integer-encoding` and `--bit-precise`: Choose How Machine Integers Are Modeled

SMACK has to encode C machine integers into SMT formulas. The default is:

```Shell
--integer-encoding=unbounded-integer
```

This treats integer values as mathematical integers. It is often faster, but it
cannot precisely model all machine-integer behavior, especially bitwise
operators, narrow casts, and wraparound-sensitive code. The abstraction can
miss a real machine-integer error, so a successful result with this encoding is
not automatically a bit-precise C-level safety result. Approximate bitwise
models can also produce spurious counterexamples.

For example:

```C
#include "smack.h"
#include <assert.h>

int main(void) {
  unsigned x = __VERIFIER_nondet_unsigned_int();
  assume(x < 4U);
  x >>= 2U;
  assert(x == 0U);
}
```

The assertion relies on bit-level shift semantics. Use bit-vectors:

```Shell
smack shift.c --integer-encoding=bit-vector
```

Older SMACK discussions and lower-level `llvm2bpl` invocations may call this
`--bit-precise`. In the `smack` frontend, the user-facing option is
`--integer-encoding=bit-vector`; internally it forwards `--bit-precise` to
`llvm2bpl`.

Wrapped integer encoding may be useful when the only required machine behavior
is arithmetic wraparound and full bit-vector reasoning is too expensive:

```Shell
smack file.c --integer-encoding=wrapped-integer
```

It models wraparound but still approximates bitwise operators. It is therefore
not the right encoding for masks or other code whose property depends on exact
bits; use `bit-vector` for those programs.

### `--check integer-overflow`: Turn C Undefined Overflow Into a Property

Signed overflow in C is undefined behavior. By default, SMACK checks user
assertions; it does not report every potential overflow unless requested.

```C
#include "smack.h"

int main(void) {
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  return x + y;
}
```

Ask SMACK to instrument overflow checks:

```Shell
smack overflow.c --check integer-overflow
```

This selects overflow checking instead of the default assertion checking. Use
`--check assertions integer-overflow` if both properties matter. The overflow
property asks whether every checked signed arithmetic operation and shift is
safe.

If only some functions matter, restrict instrumentation:

```Shell
smack overflow.c --check integer-overflow --checked-functions main
```

### `--float`: Use Precise Floating-Point Models

Without `--float`, floating-point operations are modeled with uninterpreted
functions rather than IEEE floating-point semantics. That over-approximation
can produce false alarms and counterexample traces that are not concrete C
executions.

```C
#include "smack.h"
#include <assert.h>

int main(void) {
  float x = __VERIFIER_nondet_float();
  assume(x == 0.0f);
  assert(x + 1.0f == 1.0f);
}
```

The assertion needs SMACK to understand floating-point addition and conversion
rules. Enable the floating-point model:

```Shell
smack fp.c --float
```

Some programs that mix floating-point and integer casts also need bit-vector
integers:

```Shell
smack fp_cast.c --float --integer-encoding=bit-vector
```

Floating-point reasoning is substantially heavier than unbounded integer
reasoning. Use it when the assertion depends on floating-point values, NaNs,
rounding, signed zero, or conversions.

### `--pthread`: Use the pthread Model

SMACK does not model pthreads just because a program includes `<pthread.h>`.
Enable the pthread runtime model explicitly:

```C
#include "smack.h"
#include <assert.h>
#include <pthread.h>

int x;

void *worker(void *arg) {
  x = 1;
  return 0;
}

int main(void) {
  pthread_t tid;
  pthread_create(&tid, 0, worker, 0);
  pthread_join(tid, 0);
  assert(x == 1);
}
```

Run:

```Shell
smack thread.c --pthread
```

Concurrent verification is also bounded. Increase the context bound when a bug
needs more thread interleavings:

```Shell
smack thread.c --pthread --context-bound 2
```

Use `--max-threads N` when the program can create many threads and you need a
larger or smaller thread bound.

### `--check memory-safety`: Generate Pointer Checks

User assertions are not the same as memory-safety checks. To check invalid
dereferences, invalid frees, and leaks, request the memory property:

```C
#include <stdlib.h>

int main(void) {
  int *a = malloc(2 * sizeof(int));
  int x = a[2];
  free(a);
  return x;
}
```

Run:

```Shell
smack mem.c --check memory-safety
```

This invocation selects memory safety instead of the default user-assertion
property. Use `--check assertions memory-safety` to check both.

When debugging a memory report, check the sub-properties separately:

```Shell
smack mem.c --check valid-deref
smack mem.c --check valid-free
smack mem.c --check memleak
```

### `--entry-points` and `--checked-functions`: Reduce the Target

By default, SMACK starts at `main`:

```Shell
smack file.c
```

For library-style verification, choose a different top-level function:

```Shell
smack account.c --entry-points verify_deposit
```

`--checked-functions` is different: it filters user assertions and many
source-function-local generated checks, including valid-dereference and integer
overflow checks, by the function containing the check. Assertions in functions
that do not match are omitted, even if those functions remain reachable from an
entry point. For example:

```Shell
smack account.c --check assertions valid-deref \
  --checked-functions verify_deposit
```

This filter does not cover every property. In particular, `valid-free` checks
are implemented in the shared `free` model and are not removed according to the
calling function's name.

The names are extended regular expressions, and each expression must match the
whole function name.

### `--verifier` and `--solver`: Change the Back-End

The default verifier is Corral:

```Shell
smack file.c --verifier=corral
```

Use Boogie directly for modular verification and for some solver experiments:

```Shell
smack file.c --verifier=boogie
```

Select the SMT solver with:

```Shell
smack file.c --solver=z3
smack file.c --solver=cvc5
smack file.c --solver=yices2
```

Different solvers can behave very differently on quantified formulas, arrays,
and bit-vectors.

### `-bc`, `-ll`, `-bpl`, and `-t`: Inspect What SMACK Generated

When the result is surprising, save intermediate artifacts:

```Shell
smack file.c -t -bc file.bc -ll file.ll -bpl file.bpl
```

- `-bc` saves the initial LLVM bitcode.
- `-ll` saves the final LLVM IR used by the translator.
- `-bpl` saves the generated Boogie program.
- `-t` stops after translation and skips verification.

This is the fastest way to tell whether the issue is in the frontend, SMACK's
LLVM passes, the LLVM-to-Boogie translation, or the back-end verifier.

### Less Common but Useful Options

- `--clang-options OPTIONS`
  Pass include paths, defines, target flags, or warning options to Clang.

- `--warn=silent|approximate|info`
  Control warnings about approximations and translation information.

- `--mem-mod=no-reuse-impls|no-reuse|reuse`
  Select the memory model. The default is `no-reuse-impls`.

- `--pointer-encoding=unbounded-integer|bit-vector`
  Select pointer encoding. The default is `unbounded-integer`.

- `--llvm-assumes=none|use|check`
  Control how LLVM `assume` intrinsics are handled.

- `--modular`
  Enable the experimental contracts-based modular deductive verification mode
  through Boogie.

- `--strings`
  Include SMACK's string library model.

- `--rewrite-bitwise-ops`
  Try SMACK's models for some bitwise operations when not using bit-vectors.

- `--static-unroll`
  Run LLVM's static loop unrolling pass before translation.

- `--transform-bpl COMMAND` and `--transform-out COMMAND`
  Hook custom post-processing into generated Boogie or verifier output.

For full syntax and all specialized options, run:

```Shell
smack -h
```

For workflows that combine these options, see [Running SMACK](running.md),
[Build Workflows](build-workflows.md), [Advanced Modeling](advanced.md), and
[Troubleshooting](troubleshooting.md).

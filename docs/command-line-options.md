## Command-Line Options

This page explains the options users most often need, and why those options
exist. It is checked against the `smack` parser in `share/smack/top.py`. Run
`smack -h` for the complete authoritative help text.

The general form is:

```Shell
smack [options] input-files...
```

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
smack loop.c --unroll 3
```

Use `--fail-on-loop-exit` when you want to know whether the proof depended on
cutting off a loop at the bound:

```Shell
smack loop.c --unroll 3 --fail-on-loop-exit
```

If SMACK reports:

```text
SMACK found no errors with unroll bound 3.
```

that means no error was found within that bound. It is not a proof for
arbitrarily many iterations unless the selected back-end and mode establish such
a proof.

### `--integer-encoding` and `--bit-precise`: Choose How Machine Integers Are Modeled

SMACK has to encode C machine integers into SMT formulas. The default is:

```Shell
--integer-encoding=unbounded-integer
```

This treats integer values as mathematical integers. It is often faster, but it
cannot precisely model all machine-integer behavior, especially bitwise
operators, narrow casts, and wraparound-sensitive code.

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

Use wrapped integer encoding when the program intentionally relies on modular
machine arithmetic but you do not want full bit-vector reasoning:

```Shell
smack file.c --integer-encoding=wrapped-integer
```

This is useful for code such as counters, masks, and low-level libraries where
overflow is expected behavior. It is still an abstraction, so use
`bit-vector` when the exact bit pattern matters.

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

This asks whether every checked signed arithmetic operation and shift is safe.
If only some functions matter, restrict instrumentation:

```Shell
smack overflow.c --check integer-overflow --checked-functions main
```

### `--float`: Use Precise Floating-Point Models

Without `--float`, floating-point operations are modeled approximately enough for
many control-flow questions but not for precise IEEE-style properties.

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

`--checked-functions` is different: it restricts where generated property checks
are emitted. This is useful when a large program has helper code outside the
current verification target:

```Shell
smack account.c --check memory-safety --checked-functions verify_deposit
```

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
  Enable contracts-based modular deductive verification through Boogie.

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

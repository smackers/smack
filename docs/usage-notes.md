## Usage Notes

This document shows several usage scenarios of SMACK that require special flags.
For the main task-oriented option guide, start with
[Command-Line Options](command-line-options.md).

<a id="loops-and-recusive-functions"></a>

### Loops and Recursive Functions

First of all, please keep in mind that SMACK is a *bounded* verifier, which
means that in the presence of loops and recursive functions, the verification
process unrolls them up to the bound `N` specified by the flag `--unroll <N>`.
Conceptually, unrolling a loop means transforming a loop into a sequence (length
`N`) of if-else statements, the innermost of which halts the program. Recursive
functions are handled by inlining the function `N` times and the innermost
recursive call halts the program. Therefore, not unrolling a loop or a recursive
function to a sufficient bound can lead to missed bugs. A no-errors result means
only that SMACK found no violation in the selected translation model within the
specified bound; it is not, by itself, a proof of C-level safety. Modeling
precision, such as the selected integer and floating-point encodings, is
separate from the unrolling bound.

#### Example

```C
#include "smack.h"
#include <assert.h>

int main (void) {
  long x = __VERIFIER_nondet_long();
  long y, z = 0;
  assume(x > 2);
  for (y = 0; y < x; ++ y) z++;
  assert(z != x);
  return 0;
}
```
The assertion in this program should fail. However, if SMACK is invoked with the
default unrolling bound `1`, it reports no errors. This is because the loop has
to be unrolled at least 4 times (i.e., after `y` gets value 3, the minimum value
of `x`, in the 3rd iteration) for the assertion to be reachable.

### Bitwise Operations and Integer Casts
If the program to verify contains bitwise operations or integer casts, then the
flag `--integer-encoding=bit-vector` may be required. The reason is that SMACK
uses the SMT theory of integers to encode machine integers by default, where
bitwise operations are encoded using uninterpreted functions returning
arbitrary values.  Furthermore, precise encoding is required to handle integer
signedness casts, which is not also enabled automatically.

The following program demonstrates the problems in the presence of bitwise
operations.

#### Example

```C
#include "smack.h"
#include <assert.h>

int main (void) {
  unsigned y = __VERIFIER_nondet_unsigned_int();
  assume (y < 4U);
  y >>= 2U;
  assert (!y);
}
```
This program should verify. However, if we run SMACK in its default mode, it
reports an assertion violation.

```
$ smack a.c
SMACK program verifier version 1.9.0
/home/shaobo/project/smack/install/share/smack/lib/smack.c(40,1): This assertion can fail
Execution trace:
    ...
    a.c(4,16): Trace: Thread=1  (y = -669)
    ...
    a.c(6,5): Trace: Thread=1  (y = 17)
    ...
SMACK found an error.
```

Some steps in the error trace are omitted. As you can see, the model values
of `y` in the error trace before and after the bitwise right shift operation do
not follow its semantics because it is modeled as an uninterpreted function.

In this case, we need the `--integer-encoding=bit-vector` flag that, as its
name indicates, enables bit-precise modeling of machine integers.

```
$ smack a.c --integer-encoding=bit-vector
SMACK program verifier version 1.9.0
SMACK found no errors with unroll bound 1.
```

If the program that you would like to verify contains such patterns, try
enabling this flag. However, note that enabling bit-precise reasoning often
degrades the performance of SMACK, and causes for it to take much longer to
perform the verification.

### Floating-Point Arithmetic
Similar to machine integers, floating-point numbers and arithmetic are modeled
using the theory of integers and uninterpreted functions, respectively.
Therefore, if the assertions to verify depend on precise modeling of
floating-point representations, the flag `--float` is needed. Note that
occasionally `--integer-encoding=bit-vector` has to be used in addition to
`--float`, in particular when casts between floating-point numbers and integers
are present.  Moreover, reasoning about floating-point numbers is often very
slow. Please let us know if you encounter any performance issues. We can share
some experiences that may ease the situation.

### Concurrency
Reasoning about pthreads is supported by SMACK with the flag `--pthread`. Please
use this flag when you would like to verify a multi-threaded program with
pthreads. One important flag for reasoning about concurrent programs is
`--context-bound` which is 1 by default. Try increasing this value if you would
like more thorough exploration of the concurrent programs.

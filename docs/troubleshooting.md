## Troubleshooting

This page lists common SMACK surprises and the first checks to make before
digging into the generated LLVM or Boogie.

### My Assertion Is Ignored

In C and C++, include the standard assertion header:

```C
#include <assert.h>
```

or:

```C++
#include <cassert>
```

SMACK supplies its own header that maps `assert` to verifier assertions. In C,
omitting it can produce only an implicit-declaration warning and compile the
property as an ordinary unresolved function call; C++ normally rejects the
undeclared identifier.

Also check the property selection. With no `--check` option, SMACK checks
`assertions` by default. An explicit `--check` list replaces that default, so
this checks memory safety but ignores user-written assertions:

```Shell
smack file.c --check memory-safety
```

Select both properties when both are intended:

```Shell
smack file.c --check assertions memory-safety
```

Finally, `--checked-functions` suppresses user assertions and many
function-local generated checks, such as valid-dereference and integer-overflow
checks, in functions whose names do not match. It does not filter every
property: `valid-free` checks in the shared `free` model still run.

### "No Errors" Is a Bounded, Model-Relative Result

SMACK is bounded by default. This message:

```text
SMACK found no errors with unroll bound 1.
```

means no violation of the selected properties was found in SMACK's verification
model within one loop or recursion unroll. It is not, by itself, a proof that
the C program is safe: deeper executions can expose errors, and approximate
modeling can differ from C semantics. Increase the bound for deeper executions:

```Shell
smack file.c --unroll 5
```

`--fail-on-loop-exit` does not detect an execution being cut off because its
bound was exhausted. It inserts a failing assertion on each normal loop exit.
An error from that assertion shows that a normal exit is reachable at the
chosen bound; if no loop-exit error is found, try a larger bound (unless the loop
is intentionally nonterminating).

### A Bitwise or Cast-Heavy Program Gives a Strange Counterexample

The default integer encoding uses mathematical integers, which is faster but can
approximate machine-level bit operations. Try:

```Shell
smack file.c --integer-encoding=bit-vector
```

For code that intentionally relies on modular arithmetic, also consider:

```Shell
smack file.c --integer-encoding=wrapped-integer
```

Wrapped integers model arithmetic wraparound but still approximate bitwise
operations, so they are not a substitute for bit-vectors when masks or shifts
matter. Bit-vector reasoning is usually slower, so use it when the property
depends on machine-level integer behavior.

### Floating-Point Results Look Uninterpreted

Enable floating-point modeling:

```Shell
smack file.c --float
```

Some mixed floating-point/integer programs also need bit-vector integers:

```Shell
smack file.c --float --integer-encoding=bit-vector
```

### Memory-Safety Failures Point Into SMACK Runtime Code

Generated memory-safety checks are assertions inserted by SMACK. A trace may
show a failure in `smack.c` even though the invalid pointer came from user code.
Look backward in the trace for the last assignment or call involving the failing
pointer.

When narrowing a memory issue, check one sub-property at a time:

```Shell
smack file.c --check valid-deref
smack file.c --check valid-free
smack file.c --check memleak
```

These commands intentionally select only the named memory property. Add
`assertions` to the `--check` list if user-written assertions should remain
enabled.

### Clang Cannot Find a Header

Pass include paths through `--clang-options`:

```Shell
smack file.c --clang-options="-Iinclude -Ithird_party/model/include"
```

If you compile LLVM bitcode manually, add SMACK's installed include directory to
the manual Clang invocation:

```Shell
clang-14 -c -emit-llvm -O0 -g -Xclang -disable-O0-optnone \
  -I/path/to/smack/share/smack/include file.c -o file.bc
```

Use the Clang major version that matches the LLVM version configured for SMACK
(currently LLVM 14). Manual compilation must also reproduce property-specific
frontend flags; notably, use `-fsanitize=signed-integer-overflow,shift` before
running prebuilt bitcode with `--check integer-overflow`.

### A Multi-File Program Has Unresolved Calls

Pass all source files to SMACK, or link all bitcode files with the `llvm-link`
version matching SMACK:

```Shell
smack main.c helper.c model.c
```

or:

```Shell
llvm-link-14 main.bc helper.bc model.bc -o program.bc
smack program.bc
```

### The Trace Has Poor Source Locations

Compile with debug information. SMACK does this by default for source input. If
you build bitcode manually, include `-g`:

```Shell
clang-14 -c -emit-llvm -O0 -g -Xclang -disable-O0-optnone file.c -o file.bc
```

### Boogie, Corral, or the Solver Is Not Found

Check that the verifier and solver executables are in `PATH`:

```Shell
boogie
corral
z3 --version
```

If you installed SMACK into a custom prefix, source the environment setup you
use for that installation before running tests.

### Verification Times Out

Try reducing the proof obligation before changing the program:

- Reduce the entry point with `--entry-points`.
- Restrict function-local checks with `--checked-functions`; this also
  suppresses user assertions in nonmatching functions, but does not filter
  every property (as noted above for `valid-free`).
- Lower or raise `--unroll` intentionally rather than leaving it accidental.
- Check one property at a time with `--check`.
- Try `--verifier=boogie` or a different `--solver` when the default back-end
  struggles.
- Avoid `--integer-encoding=bit-vector` unless the property needs it.

### SMACK Warns About an Approximate Translation

Approximation warnings mean SMACK continued after encountering a feature it does
not model precisely. Increase warning detail with:

```Shell
smack file.c --warn=info
```

If the warning concerns code relevant to the property, treat the result as
suspect. Reduce the program to a small regression and open an issue.

### I Need to See What SMACK Generated

Save the intermediate artifacts:

```Shell
smack file.c -t -bc file.bc -ll file.ll -bpl file.bpl
```

Then inspect:

- `file.bc` for the initial frontend output.
- `file.ll` for the LLVM IR after SMACK's LLVM passes.
- `file.bpl` for the Boogie program sent to the verifier.

This is the fastest way to distinguish a frontend issue from an LLVM-to-Boogie
translation issue.

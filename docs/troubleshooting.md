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

SMACK supplies its own header that maps `assert` to verifier assertions. Without
the include, Clang may only warn about an implicit declaration of `assert`, and
the property can be compiled as an ordinary unresolved function call.

### "No Errors" Only Means Safe Within the Bound

SMACK is bounded by default. This message:

```text
SMACK found no errors with unroll bound 1.
```

means no error was found within one loop or recursion unroll. Increase the bound
for deeper executions:

```Shell
smack file.c --unroll 5
```

Use `--fail-on-loop-exit` when you want SMACK to report executions that leave a
loop because the bound was exhausted.

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

Bit-vector reasoning is usually slower, so use it when the property depends on
machine-level integer behavior.

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

### Clang Cannot Find a Header

Pass include paths through `--clang-options`:

```Shell
smack file.c --clang-options="-Iinclude -Ithird_party/model/include"
```

If you compile LLVM bitcode manually, add SMACK's installed include directory to
the manual Clang invocation:

```Shell
clang -c -emit-llvm -O0 -g -I/path/to/smack/share/smack/include file.c -o file.bc
```

### A Multi-File Program Has Unresolved Calls

Pass all source files to SMACK, or link all bitcode files with `llvm-link`:

```Shell
smack main.c helper.c model.c
```

or:

```Shell
llvm-link main.bc helper.bc model.bc -o program.bc
smack program.bc
```

### The Trace Has Poor Source Locations

Compile with debug information. SMACK does this by default for source input. If
you build bitcode manually, include `-g`:

```Shell
clang -c -emit-llvm -O0 -g file.c -o file.bc
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
- Restrict generated checks with `--checked-functions`.
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

## Advanced Modeling

This page collects SMACK modeling mechanisms that are useful once ordinary
`assert`, `assume`, and nondeterministic inputs are not expressive enough. These
features are powerful because they affect the generated Boogie program
directly; they should be used with small regression tests and with the generated
`.bpl` inspected when possible.

### Choosing the Right Abstraction

Prefer the least invasive mechanism that expresses the verification problem:

1. Use `__VERIFIER_nondet_<type>()` for unknown inputs.
2. Use `assume` to restrict the input space.
3. Use ordinary C helper functions when the model can be written in C.
4. Use contracts when verifying functions modularly.
5. Use inline Boogie only when the model needs Boogie-level state, functions, or
   solver-specific structure.

Overly strong assumptions can make a program verify vacuously. When adding a
model, also add a failing regression that demonstrates the model can still find
the intended class of bugs.

### Nondeterministic Values and Assumptions

SMACK declares nondeterministic functions in `smack.h`:

```C
#include "smack.h"
#include <assert.h>

int main(void) {
  int x = __VERIFIER_nondet_int();
  assume(0 <= x && x < 10);
  assert(x < 10);
}
```

The call to `assume` prunes executions where the condition is false. If the
assumption is inconsistent, the verifier has no remaining executions to check,
so every assertion after it will appear to verify.

### Source-Level Contracts

Contracts are declared in `smack-contracts.h`:

```C
#include "smack.h"
#include "smack-contracts.h"
#include <assert.h>

int g;

void inc(void) {
  requires(g >= 0);
  ensures(g > 0);
  g++;
}
```

Run contract-based verification with Boogie modular mode:

```Shell
smack file.c --modular
```

The stable user-facing contract forms are:

- `requires(expr)` for preconditions
- `ensures(expr)` for postconditions
- `invariant(expr)` for loop invariants

Quantified contracts and helpers such as `old` and `result` exist in tests and
translator internals, but they are not yet exposed as a polished documented C
API in `smack-contracts.h`. Treat them as experimental until the header and
documentation are made consistent.

### Inline Boogie

SMACK recognizes several functions from `smack.h` specially:

```C
void __SMACK_code(const char *fmt, ...);
void __SMACK_decl(const char *fmt, ...);
void __SMACK_top_decl(const char *fmt, ...);
void __SMACK_mod(const char *fmt, ...);
```

`__SMACK_code` emits a Boogie statement in the current procedure.
`__SMACK_decl` emits a procedure-local Boogie declaration.
`__SMACK_top_decl` emits a top-level Boogie declaration.
`__SMACK_mod` adds a modular-verification modifies clause.

The format string uses `@` as a placeholder for later C arguments. SMACK
replaces each placeholder with the corresponding translated Boogie expression:

```C
int y = __VERIFIER_nondet_int();
__SMACK_code("@ := FOO(@);", y, x);
```

For promoted variadic arguments, use a type suffix to tell SMACK which original
C type should be translated. Common suffixes include `@i` for `int`, `@I` for
`unsigned int`, `@h` for `signed short`, `@H` for `unsigned short`, `@c` for
`char`, and `@f` for `float`.

See [Inline Boogie Code](boogie-code.md) for the full placeholder discussion.

### Custom Uninterpreted Functions

Inline Boogie is often used to introduce an uninterpreted function that abstracts
a complex operation:

```C
#include "smack.h"
#include <assert.h>

int model(int x) {
  int y = __VERIFIER_nondet_int();
  __SMACK_top_decl("function FOO(x: int): int;");
  __SMACK_code("@ := FOO(@);", y, x);
  return y;
}

int main(void) {
  assert(model(42) == model(42));
}
```

Because `FOO` is a mathematical function in Boogie, the two calls with the same
argument are equal. Add axioms only when necessary:

```C
__SMACK_top_decl("axiom (forall x: int :: FOO(x) >= 0);");
```

An inconsistent axiom set makes verification meaningless, because it can prove
anything. Keep axioms local, small, and covered by regression tests.

### Model Initialization

Use `__SMACK_INIT(name)` to emit setup code before user entry points execute.
This is useful for model state:

```C
#include "smack.h"

__SMACK_INIT(defineStates) {
  __SMACK_top_decl("const unique $idle: int;");
  __SMACK_top_decl("var $state: [ref]int;");
}

__SMACK_INIT(initStates) {
  __SMACK_code("assume (forall x: ref :: $state[x] == $idle);");
}
```

Initialization hooks are how SMACK's runtime libraries set up memory and
pthread model state. Keep declarations and assumptions separate when that makes
the model easier to inspect in the generated `.bpl`.

### Value Trace Annotations

SMACK exposes helper functions that annotate values for counterexample traces:

```C
smack_value_t __SMACK_value();
smack_value_t __SMACK_values(void *ary, unsigned count);
smack_value_t __SMACK_return_value(void);
```

These are primarily useful when writing runtime models and test harnesses where
the default trace would hide the diagnostic value you care about.

### Modeling Guidelines

- Keep C models executable-looking when possible; use inline Boogie only for
  facts that cannot be expressed cleanly in C.
- Pair every abstraction with at least one positive and one negative regression.
- Inspect `-bpl` output when adding `__SMACK_code` or top-level declarations.
- Avoid global axioms over large domains unless the property really needs them.
- Prefer `assume` for environmental constraints and `assert` for obligations.
- Do not hide unsupported behavior silently; emit a warning or keep an explicit
  failing test when the model is approximate.

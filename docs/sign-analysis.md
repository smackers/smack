## Integer Literal Sign Analysis

The `--sign-analysis` flag enables an analysis that decides, for every
negative integer literal in the LLVM IR, whether SMACK prints it as a signed
number (`-k`, spelled `$sub.i32(0, k)` in Boogie) or as the unsigned
representative of the same bit pattern (`2^N - k`). It is off by default; see
[Why the flag is opt-in](#why-the-flag-is-opt-in).

### The two-window problem

Under the default `--integer-encoding=unbounded-integer`, machine integers are
modeled by the SMT theory of unbounded integers: `$add`, `$sub` and `$mul` do
not wrap, `$zext` and `$trunc` are identities, and comparisons are the raw
integer comparisons. An `unsigned` value therefore lives in the window
`[0, 2^N)` and an `int` value in `[-2^(N-1), 2^(N-1))`. Every bit pattern with
the high bit set has two representatives, one in each window: `UINT_MAX` is
`4294967295` in the unsigned window and `-1` in the signed window.

LLVM integers are signless, and one constant object such as `i32 -1` is shared
by every use in the module, so the translator has to pick a window for each
use. If a literal is printed in a different window than the SSA value it meets,
equalities silently fail: with `u` in the unsigned window, `$eq.i32(u, -1)` is
unsatisfiable (a `u == UINT_MAX` sentinel test is never true, so a bug behind
it is missed) and `$ne.i32(u, -1)` is a tautology (a `u != UINT_MAX` guard is
never false, so the code behind it produces a false alarm).

The invariant the analysis maintains is: *every literal that meets a given SSA
value is printed in the window given by that value's inferred sign; when the
sign cannot be decided, the rendering must not break equality*.

### How a literal's window is decided

The analysis is a demand-driven oracle over exact operand uses. For a negative
literal at a given operand position it applies the following rules, in order.

1. **Arithmetic operands.** A negative literal that is a direct operand of
   `add`, `sub` or `mul` is always spelled signed, `x + (-k)`. The Boogie
   operations do not wrap, so this is the only spelling that computes the C
   decrement: `x + (2^N - k)` would never come back below `2^N`. Consumer
   evidence and sanitizer tags describe the window of the *value*, not how a
   literal must be spelled inside a non-wrapping operation, so they are not
   consulted for this position.
2. **Opcode-fixed positions.** Some opcodes fix the interpretation of an
   operand: `sdiv`, `srem`, the value operand of `ashr`, `sext`, `sitofp`,
   `getelementptr` indices and signed `icmp` predicates are signed; `udiv`,
   `urem`, `lshr`, shift amounts, `zext`, `uitofp`, unsigned `icmp` predicates
   and `select` conditions are unsigned.
3. **Flags and metadata.** A single `nsw` or `nuw` flag, or the `!overflow.sign`
   `"s"`/`"u"` tag that the sanitizer scaffolding leaves on `add`/`sub`/`mul`
   (see below), fixes the window of the values flowing into the operation.
4. **Consumer meet.** Sign-polymorphic positions (operands of `and`, `or`,
   `xor`, `shl`, `trunc`, `freeze`, the arms of a `select`, the incoming values
   of a `phi`, the arguments of a direct call and the operand of `ret`) take
   the meet of the evidence of the consumers of the result. Call arguments
   continue at the callee's parameter; return values continue at the result of
   every direct call site. `Unknown` is the identity of the meet; `Signed` met
   with `Unsigned` is `Conflict`. Because the return rule looks at every call
   site, the window of a literal inside a callee is a whole-module property.
5. **Memory and unclassified consumers.** The analysis does not follow memory.
   A store, an indirect call, an intrinsic or any other consumer it cannot
   classify counts as `Conflict`, not as "no evidence": a value that escapes
   keeps the signed spelling instead of adopting the window of whichever
   consumer happens to be visible in SSA form.
6. **Equality.** `icmp eq`/`ne` carries no sign of its own. The literal takes
   the inferred window of the other operand. When that window is `Unknown` or
   `Conflict`, the comparison is emitted as the two-window disjunction
   `$eq.iN(x, -k) || $eq.iN(x, 2^N - k)` (negated for `ne`), which is correct
   for an `x` in either window.

### Rendering policy

| Inferred sign | Spelling of a negative literal `-k` |
|---|---|
| `Unsigned` | `2^N - k` |
| `Signed` | `$sub.iN(0, k)` |
| `Unknown` | legacy heuristic for bitwise operands (`and`/`or`/`xor`/`shl`); signed elsewhere |
| `Conflict` | `$sub.iN(0, k)` |

`Conflict` prints signed. This is the choice the legacy rendering makes as
well, and it has the same limitation: an unsigned consumer of a conflicting
value sees the negative representative, so `b > 100u` on a value that is `-1`
elsewhere is unreachable in Boogie. One literal cannot serve both windows under
the unbounded encoding; the analysis only guarantees that the signed consumers
and every equality test stay correct.

### What the flag changes on the Clang command line

The IR that Clang emits at `-O0` does not say whether an `add` came from signed
or unsigned source arithmetic. With `--sign-analysis`, SMACK asks Clang to keep
that information by compiling user sources (never library or model sources)
with

```
-fsanitize=signed-integer-overflow,unsigned-integer-overflow
-fsanitize-trap=signed-integer-overflow,unsigned-integer-overflow
```

Clang then emits `llvm.sadd.with.overflow`/`llvm.uadd.with.overflow` (and the
`sub`/`mul` variants) instead of plain arithmetic. An early annotation-only
run of SMACK's integer overflow pass lowers each intrinsic back to a plain
`add`/`sub`/`mul` tagged with `!overflow.sign` `"s"` or `"u"` and removes the
unreachable trap branch. The trap mode keeps Clang from generating UBSan
handler calls and data descriptors. When `--check=integer-overflow` is also
given, the regular overflow checks are generated as before and the trap flag
is not added.

`--clang-options` is appended *after* these flags when the analysis is on, so an
explicit `--clang-options=-fno-sanitize=signed-integer-overflow,unsigned-integer-overflow`
opts out of the instrumentation. The analysis then only sees `nsw`/`nuw` flags
and consumer evidence, which is also the situation for uninstrumented bitcode
passed directly to `smack`. When the analysis is off, `--clang-options` keeps
its historical position on the command line.

### Encodings where the flag is irrelevant

Under `--integer-encoding=bit-vector` every literal is a bit-vector and the two
spellings denote the same value. Under `--integer-encoding=wrapped-integer`
arithmetic wraps modulo `2^N` and values are normalized before comparison, so
the choice of window does not affect verdicts either. The analysis only matters
for the default unbounded-integer encoding.

### Why the flag is opt-in

With the flag off the generated Boogie is byte-identical to previous releases,
including the legacy spelling of negative literals (for example `x - -2` on
an `int` printed as `$sub.i32(x, 4294967294)`, which is wrong under the
unbounded encoding). The analysis fixes these renderings, but it also changes
the Clang command line, adds an IR cleanup pass before translation, and changes
the spelling of every negative literal in the program. The first version of the
analysis was found to break sentinel equalities, unsigned countdown loops and
values that flow through memory; those cases are fixed and now covered by the
`test/c/basic/sign_analysis_*.c` regressions, each of which pairs a verified
program with a failing twin. Until the analysis has been validated on larger
corpora the default stays unchanged, and `--sign-analysis` is the way to enable
it:

```
smack a.c --sign-analysis
```

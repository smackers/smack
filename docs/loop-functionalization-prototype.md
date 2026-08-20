# LLVM loop functionalization prototype

## Reconnaissance (Phase 1)

This checkout is pinned to LLVM 14 (`bin/versions`) and builds against the
LLVM 14 legacy pass manager.  The relevant pipeline is assembled explicitly
in `tools/llvm2bpl/llvm2bpl.cpp`.  C/C++ input is compiled at `-O0` with
`optnone` disabled, then SMACK runs mem2reg and its own normalization passes.
`LoopSimplify` and `LoopRotate` run only under `--static-unroll` (and
`LoopSimplify` is also required by `--fail-on-loop-exit`); the normal pipeline
does not run LCSSA, `IndVarSimplify`, `LoopAccessAnalysis`, MemorySSA, or
`LoopIdiomRecognize`.  In particular, SMACK does not currently get the usual
memset/memcpy loop recognition from an optimization pipeline.  Clang may emit
memory intrinsics directly, and SMACK already lowers those in `SmackRep`, but
ordinary `-O0` element loops remain loops.

`SmackModuleGenerator` is the last LLVM pass and requests per-function
`LoopInfoWrapperPass` before constructing a `SmackInstGenerator`.  The latter
turns each LLVM basic block into a Boogie block and each branch into a `goto`,
so LLVM backedges become ordinary cyclic Boogie control flow.  SMACK has
passes that rewrite LLVM CFGs (`NormalizeLoops`, `AnnotateLoopExits`, and
contract extraction), but it has no loop-summary abstraction.

LLVM 14 exposes all of the proposed analyses to this legacy pipeline:

- `ScalarEvolutionWrapperPass` provides trip counts and `SCEVAddRecExpr`
  recurrences.  On the motivating `a[i] = i` loop in this pipeline it reports
  the IV as `{0,+,1}<L>`, the address as `{a,+,4}<L>`, and the exact symbolic
  backedge count as `n`.
- `AAResultsWrapperPass`, `MemorySSAWrapperPass`, and
  `LoopAccessLegacyAnalysis` are the LLVM 14 legacy wrappers.  None is
  currently requested or queried by SMACK's generator.  `LoopAccessAnalysis`
  is useful supporting evidence, but its vectorization condition is weaker
  than functionalization's entry-memory condition and must not be used as the
  proof by itself.
- MemorySSA's walker can identify the nearest may-clobbering definition of a
  load.  For this prototype it can corroborate that a load reaches loop-entry
  memory; a separate all-iterations alias/dependence argument is still needed.

SMACK memory is not one source-level array per object.  `Regions` partitions
LLVM memory and `SmackRep` declares `$M.<region>` as either a scalar singleton,
a typed `[ref] T` map, or a byte map.  Loads and stores use typed helpers such
as `$load.i32(M,p)` and `$store.i32(M,p,v)`; bytewise and unsafe variants have
different encodings.  A first map-lambda prototype should consequently accept
only non-singleton, non-bytewise typed regions and update the existing
`$M.<region>` rather than inventing a new array model.

`BoogieAst` supports map select/update, ITEs, and quantifiers, but has no lambda
expression node.  Adding a small lambda AST node is sufficient to print
Boogie's `(lambda p: ref :: e)` syntax.  A smoke test against the requested
`~/corral` checkout confirms that its Boogie 3.5.7 parser and type checker
accept that syntax.  The checkout now expands lambdas before its custom VC
translation, so raw SMACK lambda output is accepted end to end without an
external lifting step.

## Prototype architecture

The least invasive insertion point is between LLVM analysis and instruction
emission, inside the existing module/instruction generators:

1. A separate recognizer consumes `LoopInfo`, ScalarEvolution, AA, and
   MemorySSA and constructs a `FunctionalLoopSummary`.
2. `SmackInstGenerator` emits the summary in the loop preheader, jumps directly
   to the unique exit, and suppresses the original loop blocks.  The LLVM IR is
   deliberately left intact so `Regions` still sees the real typed accesses.
3. The emitter snapshots every referenced `$M.<region>` and assigns the
   destination map a lambda whose false branch reads the destination snapshot.
   RHS loads read only source snapshots.

The initial recognizer will require a top-tested, single-level loop with a
preheader, one latch, one exit, one affine unit IV starting at zero, an exact
symbolic-or-constant SCEV trip count, and one injective affine store.  It will
accept only a deliberately small RHS tree (constants, the IV, loop invariants,
entry-memory loads, and selected integer casts/arithmetic).  Every possibly
aliasing store/load pair must either be proven disjoint for all iterations or
the loop is rejected.  Calls, assertions/assumptions, volatile or atomic
accesses, exceptional/abnormal exits, bytewise memory, escaping loop values,
and unsupported integer/pointer encodings are rejected.

This placement is also the safety boundary.  Memory-safety and overflow
instrumentation run before Boogie generation.  A loop containing their calls
will fail recognition, so functionalization cannot silently erase a per-
iteration assertion.  Source-location/debug intrinsics are non-semantic and
may be omitted with the suppressed loop blocks.

The core soundness obligations for an accepted summary are: the SCEV trip
count exactly describes the body iterations; the store recurrence is
injective (`W(j) != W(k)` for `j != k`); every RHS load denotes loop-entry
memory (`j < k => W(j) != R(k)`); the emitted expression uses the same SMACK
integer, pointer, and typed-memory operations as ordinary lowering; and no
observable scalar or control-flow effect is discarded.

## Implemented prototype

The opt-in `--functionalize-loops` implementation now supports this exact
class:

- a non-nested LoopSimplify loop with one latch, one conditional exit and one
  unique exit block; both top-tested and LoopRotate-style bottom-tested forms
  are accepted, including a zero-trip guard outside the loop;
- straight-line control flow or one structured `if`/`else` diamond;
- one unique integer SCEV recurrence `{0,+,1}<L>` defining iteration `k`, and
  a body-execution count that simplifies to a constant or one loop-invariant
  LLVM value of the same type;
- one or more simple stores with positive-constant-stride affine pointer
  recurrences `base + offset + stride*k`.  Address injectivity must follow
  from SCEV no-wrap or an LLVM `inbounds` GEP;
- pairwise stores that AA proves object-disjoint, whose affine images are
  disjoint by the stride/offset congruence test, or that write the identical
  pointwise address under opposite sides of the same branch;
- RHS values composed from constants, loop invariants, the iteration, modular
  affine scalar SCEV recurrences, `add`/`sub`/`mul`, constant-safe integer
  division/remainder, integer casts, comparisons, selects, and affine loads;
- a final escaping unit induction, including the one-input LCSSA forwarding
  PHI produced by LLVM 14 loop rotation, when SCEV proves its exit value is the
  trip count;
- non-singleton, non-bytewise typed SMACK regions under the default integer
  and pointer encodings.

Recognition is semantic rather than source-pattern based.  For example,
derived pointer inductions such as `{a,+,8}<L>` are accepted even when the
source no longer has a canonical `a[2*i]` expression, and an RHS scalar
recurrence `{0,+,2}<L>` is emitted as modular `2*k`.  Conversely, a source
expression such as 32-bit `2*i` is rejected if LLVM cannot prove its pointer
recurrence because the multiply may wrap.

For every load/store pair that AA cannot separate, the recognizer requires
identical pointwise recurrences with the load dominating the write, or affine
images proven disjoint for all iterations.  MemorySSA must independently
place object-disjoint loads at loop entry; a same-object MemoryPhi is bypassed
only when the recurrence proof discharges its conservative may-clobber.  Each
store recurrence is injective, and separate stores cannot collide except for
mutually exclusive alternatives at the same pointwise address.

The emitter snapshots every referenced SMACK memory map before any update.
It groups writes by destination map and emits one lambda with nested guarded
ITEs per map.  For a lambda address `p`, it reconstructs candidate iteration
`k`, checks `0 <= k < T` and `p == W(k)`, and evaluates every guard and RHS from
the entry snapshots.  The default branch also reads the entry destination
map.  Thus lambda assignment order cannot turn an entry-memory read into a
read of a newly written map.  The emitter assigns the supported final
induction state, jumps to the original exit and omits every loop block, so the
generated Boogie has no cycle for that LLVM loop.

The implementation deliberately rejects nonzero-start or non-unit domain
inductions, negative or non-affine addresses, scatter, unproved aliasing,
overlapping nonexclusive stores, loop-carried RAW dependences, nested loops,
more than one body diamond, abnormal/multiple exits, arbitrary escaping
scalars, calls, assertions/assumptions, memory intrinsics, volatile/atomic
accesses, EH, bytewise/singleton regions, memory-model debugging, and
bit-precise/wrapped integer or pointer configurations.  Division by a variable
or zero-capable divisor is also rejected.  Instrumented safety/overflow checks
introduce unsupported loop effects before recognition, so functionalization
does not erase their per-iteration failures.

## Regression and evaluation results

The focused suite covers constant, IV, remainder and affine-scalar-recurrence
fills; disjoint copy-plus-constant; same-object entry-memory updates; multiple
maps and interleaved disjoint writes; rotated constant and symbolic loops;
guarded one- and two-sided stores; and final-IV/LCSSA state.  Negative tests
retain ordinary loops for shifted loop-carried RAW, write-before-read,
overlapping writes, scatter, possible aliasing and an invalid instrumented
memory access.  All tests run with loop bound 1 and inspect the generated
Boogie for the expected presence or absence of lambda summaries.  The suite
also covers preserving a rejected loop's known bound and conservatively
rejecting a complex header recurrence without recursing through it in LLVM 14
ScalarEvolution.  All 72 test/memory-model configurations pass with Boogie.

Loop-bound warnings are deferred until semantic and memory-model eligibility
are known.  Summarized loops no longer request a higher bound; rejected loops
retain the warning.

For the fixed 4096-iteration demonstration, baseline Boogie has 16,269 lines /
707,389 bytes and a cycle; functionalized Boogie has 16,233 lines / 706,338
bytes, one lambda and no source-loop cycle.  With the requested `~/corral` and
recursion bound 1, baseline reaches the recursion bound (0.84 s), while the raw
lambda proves the assertions (1.13 s).  A symbolic-`n` fill has the same
qualitative result.  Symbolic `a[i] = a[i] + 1` changes from 16,384 lines /
712,133 bytes to 16,332 lines / 710,485 bytes; baseline reaches bound 1
(0.92 s), whereas the lambda proves (1.25 s).

The official SV-COMP frontend (`-x svcomp --verifier=svcomp`) was used for the
suite study.  That frontend itself enables `--static-unroll`, so LLVM loop
rotation is part of these results even though no explicit unroll flag was
added to the commands.

| suite | tasks | translated | tasks with summaries | summaries | baseline bytes on affected tasks | functional bytes |
|---|---:|---:|---:|---:|---:|---:|
| C.unreach-call.Arrays | 440 | 438 | 63 | 217 | 95,707,143 | 95,504,377 |
| C.unreach-call.Loops | 758 | 758 | 7 | 7 | 4,957,197 | 4,951,224 |
| C.unreach-call.SoftwareSystems-DeviceDriversLinux64 | 2,326 | 2,180 | 32 | 37 | 222,089,115 | 222,063,060 |

On Arrays, the original 44 affected tasks were checked with a 20-second outer
limit: every baseline timed out, while functionalization found 10 expected
unsafe verdicts and timed out on 34 (including all safe tasks).  The 19 tasks
added by later multiple-store, guarded and scalar-recurrence extensions were
checked at 10 seconds; both variants timed out because other initialization or
assertion loops remain cyclic.  On the final seven affected Loops tasks at 10
seconds, every baseline timed out; functionalization solved three (one unsafe
and two safe) and timed out on four.

The driver scan used a 30-second translation-only limit and did not invoke a
verifier.  Its 146 misses comprise 134 failures in the existing SeaDsa pass,
six timeouts, and six generator failures.  Five generator failures reproduce
without functionalization; the sixth succeeded on an immediate isolated
retry.  Before the robustness fix, ten additional files crashed because the
deferred loop-bound warning path queried LLVM 14 ScalarEvolution after
`NormalizeLoops`; all ten now translate, and one newly reachable `cxgb3` loop
is summarized.  Trip counts are now recorded as metadata before normalization,
and warning emission consumes that metadata after summary eligibility is
known.  Recognition also selects the canonical induction before asking SCEV
about recurrences and rejects complex non-induction header PHIs with a cheap
structural screen.

Longer retries translated three of the six timed-out files, without finding
summaries.  Retrying `hisax` and the two `bfa` files was stopped after their
concurrent `llvm2bpl` processes consumed roughly 8--14 GiB each and triggered
the host OOM killer; those resource-limited retries are not counted in the
table.

The low Loops hit rate is informative.  Most of its 758 tasks are scalar or
nonlinear recurrence problems, not pointwise memory updates.  Representative
remaining array cases require one of the following qualitatively new ideas:

- per-iteration nondeterministic calls need a fresh-function/havoc-map summary
  plus a proof that call and assumption behavior is preserved;
- nondeterministic scatter needs injectivity or address inversion;
- reductions, sorting and in-place mutation need closed forms for loop-carried
  scalar or memory state;
- read-only assertion loops need a quantified safety summary rather than a
  memory lambda;
- arrays initialized through `llvm.memset` become bytewise SMACK regions, so a
  typed pointwise lambda would require byte packing/unpacking support.

These are the current fundamental boundaries of this prototype rather than
small additions to its pointwise recognizer.  The recommended next experiment
is quantified summarization of read-only assertion loops: it would directly
address why many successfully functionalized initialization loops still time
out, without weakening the entry-memory soundness argument.

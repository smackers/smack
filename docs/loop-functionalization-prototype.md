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

The recognizer deliberately keeps three semantic summary forms separate.
Memory-update loops produce map lambdas.  Pure early-exit checks produce a
quantified predicate and a failure witness.  Read-only verifier loops produce
an exact quantified assertion or assumption.  All three consume the same SCEV
induction, iteration-domain, affine-address and RHS representation, so
recognition and proof remain independent of Boogie emission.

This placement is also the safety boundary.  Memory-safety and overflow
instrumentation run before Boogie generation.  A loop containing their calls
will fail recognition, so functionalization cannot silently erase a per-
iteration check.  The only admitted calls are a single reserved
`__VERIFIER_assert` or `__VERIFIER_assume`, for which the summary explicitly
recreates SMACK's verifier semantics.  Source-location/debug intrinsics are
non-semantic and may be omitted with the suppressed loop blocks.

The core soundness obligations for an accepted summary are: the SCEV trip
count exactly describes the body iterations; the store recurrence is
injective (`W(j) != W(k)` for `j != k`); every RHS load denotes loop-entry
memory (`j < k => W(j) != R(k)`); the emitted expression uses the same SMACK
integer, pointer, and typed-memory operations as ordinary lowering; and every
observable scalar, control-flow, assume, or error effect is preserved.

## Implemented prototype

The opt-in `--functionalize-loops` memory-update implementation now supports
this exact class:

- a non-nested LoopSimplify loop with one latch, one conditional exit and one
  unique exit block; both top-tested and LoopRotate-style bottom-tested forms
  are accepted, including a zero-trip guard outside the loop;
- straight-line control flow or one structured `if`/`else` diamond;
- one unique integer SCEV recurrence with a loop-invariant start and a strictly
  positive constant step.  Its exact body-execution count may be a supported
  loop-invariant SCEV expression (constants/unknowns, integer casts, add/mul,
  and unsigned division by a nonzero constant);
- one or more simple stores with positive-constant-stride affine pointer
  recurrences `base + offset + stride*k`.  Address injectivity must follow
  from SCEV no-wrap or an LLVM `inbounds` GEP;
- pairwise stores that AA proves object-disjoint, whose affine images are
  disjoint by the stride/offset congruence test, whose finite ranges are
  disjoint for a constant trip count, or that write the identical pointwise
  address under opposite sides of the same branch.  Different invariant bases
  may be normalized through inbounds constant GEPs to one base plus offsets;
- RHS values composed from constants, loop invariants, the iteration, modular
  affine scalar SCEV recurrences, `add`/`sub`/`mul`, constant-safe integer
  division/remainder, integer casts, comparisons, selects, and affine loads;
- a final escaping induction, including the one-input LCSSA forwarding PHI
  produced by LLVM 14 loop rotation, when SCEV proves its exit value is
  `start + step*tripCount`;
- non-singleton, non-bytewise typed SMACK regions under the default integer
  and pointer encodings.

Recognition is semantic rather than source-pattern based.  For example,
derived pointer inductions such as `{a,+,8}<L>` are accepted even when the
source no longer has a canonical `a[2*i]` expression, and an RHS scalar
recurrence `{0,+,2}<L>` is emitted as modular `2*k`.  Conversely, a source
expression such as 32-bit `2*i` is rejected if LLVM cannot prove its pointer
recurrence because the multiply may wrap.  LLVM 14's common
`base + zext({0,+,1}<L>)` form is accepted when the casted recurrence is the
validated zero-start/unit-step induction; broader casted recurrences remain
rejected without a no-wrap proof.

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

The memory-update form deliberately rejects negative or
non-constant-step inductions, non-affine addresses, scatter, unproved aliasing,
overlapping nonexclusive stores, loop-carried RAW dependences, nested loops,
more than one body diamond, abnormal/multiple exits, arbitrary escaping
scalars, all calls (including assertions/assumptions), memory intrinsics,
volatile/atomic accesses, EH, bytewise/singleton regions, memory-model
debugging, and
bit-precise/wrapped integer or pointer configurations.  Division by a variable
or zero-capable divisor is also rejected.  Instrumented safety/overflow checks
introduce unsupported loop effects before recognition, so functionalization
does not erase their per-iteration failures.

### Read-only predicate summaries

The second exact form handles pure search/check loops of the form “return a
constant on the first failing element, otherwise return another constant.”
It currently requires a LoopSimplify loop with one bound exit, one early exit,
one positive affine induction, no escaping loop value, and one or more simple
affine loads used by a straight-line Boolean predicate.  Every non-debug
instruction must belong to the bound, induction update, or predicate slice;
stores, calls, additional conditionals, volatile/atomic loads and direct exit
PHIs are rejected.

The successful path assumes the exact iteration-quantified predicate.  It also
assumes a logically redundant pointer-quantified form over the affine read
image: its explicit memory-read trigger lets client reads instantiate the fact
without requiring the solver to invert pointer arithmetic.  The failing path
havocs an iteration witness and assumes that it is in the exact domain and
violates the predicate.  The original normal/failure exit blocks remain in the
program, so their constant return and join-PHI behavior is preserved; only the
loop blocks are omitted.  This is exact because the loop is read-only and no
iteration-dependent value escapes.

Read summaries reuse `SmackRep`'s actual typed/byte load expression.  They may
therefore read non-singleton bytewise maps and type-collapsed `[ref] i8` maps,
even though those regions remain deliberately forbidden for lambda writes.
This distinction is important for AWS's `aws_is_mem_zeroed`, which views a
mixed-field struct through `uint8_t *`.

### Read-only verifier summaries

The third exact form handles a deliberately narrow verifier loop:

```c
for (unsigned i = 0; i < n; ++i)
  __VERIFIER_assert(P(entry_memory, i));
```

and the corresponding `__VERIFIER_assume` loop.  Source `assert(P)` is also
accepted in the LLVM 14 shape emitted by SMACK's `assert.h`: a predicate branch
whose failing arm calls `__VERIFIER_assert(0)` and then rejoins.  Direct
nonzero-valued verifier conditions are accepted without requiring that branch
shape.

The loop must have one exact SCEV trip count, one positive affine induction,
one verifier call, at least one simple affine load, no stores, no escaping
values, no other calls or conditionals, no exit PHI, and no abnormal exit.
Top-tested loops and LoopRotate bottom-tested loops are supported.  In the
bottom-tested case the verifier predicate must dominate the exit test, and the
zero-trip preheader guard is retained, so adding one to SCEV's backedge count
does not invent an execution.

For an assertion, the normal branch assumes `forall k in [0,T). P(k)`.  The
error branch havocs an in-domain witness satisfying `!P(k)`, emits an
`assert false` annotated with the original source location, and then targets
the original exit.  Choosing an arbitrary failing iteration rather than the
first one is exact because the accepted body is read-only and has no other
observable effect.  An assumption loop emits only the universal assumption;
it has no failure witness or error branch.  Both forms add a redundant
pointer-triggered universal formula, as the early-return summary does, so a
client read can instantiate the fact without solving affine address inversion.

This treatment relies on SMACK's reserved verifier-function contract for the
names `__VERIFIER_assert` and `__VERIFIER_assume`.  Arbitrary user-defined
functions with those reserved names are outside the supported input contract.
An explicit LLVM attribute or metadata marker would be preferable before
generalizing the call whitelist.

A translation-only run of
`aws_array_list_init_dynamic_harness.i` from AWS-C-Common now replaces the
reachable `aws_is_mem_zeroed` loop with this acyclic summary.  No verifier was
run on the AWS or driver suites.  Representative region traces also explain
why region-only store disjointness was not added: one AWS fill had a useful
typed `i8` region, but priority-queue and driver structures collapsed multiple
fields into one region, while a representative copy placed source and
destination in the same region.  The existing AA plus affine-image proofs are
more useful and no less conservative for those loops.

## Regression and evaluation results

The focused suite covers constant, IV, remainder and affine-scalar-recurrence
fills; disjoint copy-plus-constant; same-object entry-memory updates; multiple
maps and interleaved disjoint writes; rotated constant and symbolic loops;
guarded one- and two-sided stores; nonzero starts, safe positive steps, and
final-IV/LCSSA state.  Negative tests
retain ordinary loops for shifted loop-carried RAW, write-before-read,
overlapping writes, scatter, possible aliasing and an invalid instrumented
memory access.  All tests run with loop bound 1 and inspect the generated
Boogie for the expected presence or absence of lambda summaries.  The suite
also covers preserving a rejected loop's known bound and conservatively
rejecting a complex header recurrence without recursing through it in LLVM 14
ScalarEvolution.  Read-only tests cover symbolic `all_zero`, two-array
equality, a type-collapsed struct byte scan, rejection when the failing index
escapes, and preservation of an invalid memory access.  Verifier-loop tests
cover safe and failing source assertions, a direct `__VERIFIER_assert`, a
two-array predicate, a direct `__VERIFIER_assume`, LoopRotate form, and
rejection of an instrumented invalid access.  All 120 test/memory-model
configurations pass with Boogie at loop bound 1.  Safe and failing assertion
clients also produce the expected results with the updated `~/corral` at bound
1.

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

The larger SV-COMP Arrays example
`array-examples/standard_init8_ground-2.i` contains eight 100,000-iteration
fills followed by a 100,000-iteration direct assertion loop.  Baseline Boogie
has 16,533 lines / 717,901 bytes and retains all nine source loops.
Functionalized Boogie has 16,261 lines / 676,623 bytes, eight lambdas, two
universal assertion formulas and no source-loop cycle.  The updated
`~/corral` reports no error at bound 1; the only remaining loop warning is the
unreachable library implementation of `abort`.

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
- verifier loops with multiple assertion/assumption sites, other calls, stores,
  or inserted access checks need an ordered verifier-action summary and, for
  memory safety, a range-validity proof over every accessed address;
- arrays initialized through `llvm.memset` become bytewise SMACK regions, so a
  typed pointwise lambda would require byte packing/unpacking support.

These are now the fundamental boundaries of the exact pointwise model rather
than small additions to its recognizer.  The recommended next experiment is to
mark verifier primitives explicitly in LLVM and represent a short ordered list
of pure assertion/assumption sites.  Instrumented memory-safety and undefined-
behavior checks should remain rejected until their per-iteration validity can
be expressed and tested over the complete address image.

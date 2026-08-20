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

The opt-in `--functionalize-loops` implementation supports exactly this class:

- a non-nested LoopSimplify loop with one latch, a conditional header exit,
  one unique exit block, and otherwise straight-line branches;
- exactly one integer SCEV add recurrence `{0,+,1}<L>` and an exact exit count
  that is either a constant or one loop-invariant LLVM value of the same type;
- exactly one simple store whose pointer SCEV is an affine, positive-constant-
  stride, no-self-wrap recurrence with a loop-invariant pointer base;
- an RHS composed of integer constants, the IV, loop-invariant SSA values,
  `add`/`sub`/`mul`, selected integer casts, and simple loads with affine
  addresses;
- for every RHS load, either LLVM AA proves the entire underlying source and
  destination objects `NoAlias` and MemorySSA's clobber is loop entry or
  outside the loop, or its affine recurrence is exactly the store recurrence;
- non-singleton, non-bytewise typed SMACK regions, using the default unbounded
  integer and pointer encodings.

The emitter snapshots every source/destination region, derives the unique
iteration number from the lambda's address parameter, checks both the
iteration domain and exact address reconstruction, computes the RHS from the
snapshots, and otherwise returns the old destination-map element.  It then
jumps from the preheader to the old unique exit and emits none of the loop's
blocks.  Escaping values (including a live final IV) are rejected rather than
approximated.

The identical-recurrence case covers `a[i] = a[i] + c`: a positive,
no-self-wrap recurrence is injective, so for `j < k`, `W(j) != R(k)` when
`R(k) = W(k)`.  The load is an SSA dependency of the sole store and therefore
occurs before that iteration's write.  It consequently reads the loop-entry
value at that address even though MemorySSA conservatively reports the loop's
memory phi as its clobber.

The prototype deliberately rejects multiple stores, shifted or otherwise
non-identical same-object read recurrences, non-unit or nonzero-start IVs,
computed scatter addresses, possible aliasing, nested or branched bodies,
exit PHIs, calls, assertions/assumptions, memory intrinsics, volatile/atomic
accesses, EH, bytewise/singleton regions, memory-model debugging, and
bit-vector or wrapped integer/pointer encodings.  Memory-safety instrumentation
inserts calls in the loop before recognition, so `--check=memory-safety`
candidates are rejected and their per-iteration checks remain in cyclic
control flow.

## Regression and evaluation results

`test/c/functionalize-loops` contains symbolic positive tests for constant
fill, IV fill, `restrict`-disjoint copy-plus-constant, and same-object
pointwise addition; a fixed 4096-iteration demonstration; and negative tests
for loop-carried and shifted RAW recurrences, scatter, possible aliasing, and
an invalid memory access under memory-safety checking.  The positives inspect
generated Boogie for a lambda; the negatives inspect it for absence of a
summary.  All 30 combinations of these ten tests and SMACK's three memory-
allocation models pass with Boogie (loop bound 1).

Loop-bound warnings are deferred when functionalization is enabled until the
generator has completed semantic recognition and memory-model eligibility
checking.  Successfully summarized loops no longer produce a misleading
request for a higher `--unroll` value; rejected loops, including memory-safety
and bit-vector configurations, retain the warning.

For the fixed 4096-iteration test, raw generated Boogie changed as follows:

| configuration | lines | bytes | lambda summaries | cyclic source loop |
|---|---:|---:|---:|---|
| baseline | 16,269 | 707,389 | 0 | yes |
| functionalized | 16,233 | 706,338 | 1 | no |

Using the requested `~/corral` with recursion bound 1, the baseline reports
`Reached recursion bound of 1` (0.84 s wall time), whereas the functionalized
raw-lambda program proves all three assertions without reaching the bound
(1.13 s wall time).  The analogous symbolic-`n` test has the same qualitative
result: baseline reaches the bound; functionalized proves with bound 1.

For symbolic `a[i] = a[i] + 1`, raw Boogie shrinks from 16,384 lines / 712,133
bytes to 16,332 lines / 710,485 bytes and contains one lambda summary instead
of the source cycle.  With the same requested Corral executable and recursion
bound 1, the baseline reaches the bound (0.92 s wall), while the raw-lambda
functionalized input proves the arbitrary-index assertion without reaching
the bound (1.25 s wall).  Running both examples through the complete
`smack --functionalize-loops --verifier=corral --unroll=1` path also succeeds.

The recommended next SMACK experiment is either multiple stores with pairwise
disjoint affine recurrences or a single-store diamond whose values merge into
an ITE.  Multiple stores exercises the summary representation and cross-store
dependence proof; an ITE body exercises control dependence.  Both should
retain the current conservative memory-model and instrumentation boundary.

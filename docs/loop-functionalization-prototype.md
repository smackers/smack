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
accept that syntax.  The currently built Corral executable nevertheless lets
the lambda reach the low-level VC translator, which crashes; its input path
still needs to invoke Boogie's lambda-lifting/expansion hook before this can be
counted as end-to-end verification.

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

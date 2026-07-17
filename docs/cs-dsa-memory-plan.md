# Context-Sensitive DSA Memory Regions in SMACK

## Overview

SMACK runs SeaDsa in context-sensitive mode (`-sea-dsa=cs`) and constructs a
region vector for each LLVM function. Region indices are local to a function;
they are never compared across functions without a SeaDsa mapping.

The existing `cs` branch uses a hybrid backing policy. Entry-function regions
and larger cross-function classes use module-level maps, while selected small
classes are threaded through procedure inputs and outputs. The soundness fixes
below preserve that policy for ordinary runs; under
`-local-private-memory-maps` (enabled automatically for SV-COMP, where Corral
runs with `/trackAllVars`), provably function-private stack/heap regions stay
procedure-local instead (see Backing Maps).

## Soundness Invariants

1. A region mapping is a relation, not necessarily a function. One callee
   region can correspond to several caller regions after DSA or region merges.
2. Every association in that relation is preserved. Selecting one target can
   disconnect caller state and is an unsound under-approximation.
3. A relation with several targets cannot be represented by one threaded map
   argument. Its complete equivalence class must use shared backing storage.
4. Region construction and call-site mapping must converge before translation
   continues. Hitting the iteration limit is a translation error.
5. A nonfunctional SeaDsa `SimulationMapper` is a translation error until its
   complete relation can be consumed through a SeaDsa API.
6. Cross-graph global translation is either exact and offset-preserving or
   conservative. It never silently falls back to an unrelated cell or offset
   zero.

## Analysis Phases

### 1. Per-Function Regions

Loads, stores, atomics, and memory intrinsics create field-granular regions in
the DSA graph of the function containing the access. Regions are not pre-seeded
from whole formals, actuals, or globals because whole-object probes collapse
otherwise disjoint fields.

`__SMACK_static_init` and `__SMACK_init_func*` are emitted in the entry
function's memory context. Their cells are translated through the identity of
the exact underlying global. If exact field translation is unavailable, SMACK
uses a whole-node bytewise region in the entry graph. Values in init bodies
that are not rooted at any global (stack arrays, call results) are not shared
global memory; they anchor as ordinary regions in the entry context rather
than aborting translation.

### 2. Direct Access Sets

Each function records directly read and modified regions:

- load: read
- store: modified
- atomic read-modify-write: read and modified
- `memset`: modified
- `memcpy`/`memmove`: source read and destination modified

### 3. Call-Site Relations

`Graph::computeCalleeCallerMapping` supplies SeaDsa's authoritative mapping for
globals, return values, formal/actual parameters, and reachable links. SMACK
maps every callee region cell into the caller and records:

```text
callee region -> { caller region, ... }
```

The computation runs to a structural fixpoint because mapping a reachable cell
can create or merge caller regions. Deep pointer-passing call chains propagate
one level per pass under adverse module order, so the iteration bound scales
with the number of functions; exceeding it aborts translation.

### 4. Merge Propagation and Normalization

If several callee regions map to one caller region, the callee regions are
merged. All index-based tables are repaired after every erase. Mapping-key
collisions union their target sets instead of discarding one mapping.

Normalization retains the branch's pairwise merge algorithm for incomplete,
complicated, collapsed, and interval-overlapping regions.

### 5. Global Relations

For each ordinary function, global-backed regions are related to every matching
entry-function region. This table is relational. Exact global identity is also
tracked when preserving singleton scalar regions; merging views from different
globals demotes the result to a map.

Statically initialized globals retain the branch's conservative map encoding.

### 6. Backing Maps

A union-find structure links region pairs through call-site and global
relations. In the default mode:

- entry regions keep their module-level declarations;
- small classes with two same-function regions and at most eight members can
  remain threaded through procedure interfaces;
- other cross-function classes use entry-owned or shared module-level maps;
- accessed regions outside mapped classes get module-level maps of their own.

Before backing maps are chosen, a preliminary procedure-interface pass runs in
every context-sensitive mode: a callee interface region that lacks a caller
counterpart at even one call site (for example, a pointer formal receiving
null) cannot be threaded through one fixed Boogie signature and is forced onto
a shared map.

Classes containing a non-unique relation are excluded from threading. If a
non-threaded class contains several regions from one function, selecting one
of them as its owner would disconnect the others, so that class uses one shared
map. This is a representational soundness requirement, not a memory-splitting
or map-count optimization.

Under `-local-private-memory-maps` (automatic for `-x svcomp`, where Corral's
`/trackAllVars` removes the abstraction advantage of globals), the policy
changes for provably private memory: singleton classes and unmapped leftover
regions that are allocated (stack/heap) and hold no global stay
procedure-local, and the blanket module-level promotion of entry regions is
skipped. Global-backed, external, unknown, and cross-function regions remain
module-level in both modes.

### 6a. Dead Static-Initializer Maps

After translation, `__SMACK_static_init` stores whose target map has no other
occurrence anywhere in the printed program are removed and the map's
declaration is suppressed. The liveness check counts every textual occurrence
of each entry/shared map name over the whole program, so any reference outside
the candidate stores conservatively keeps the map. This runs only under
context-sensitive DSA.

### 7. Access Closure and Interfaces

Callee reads and modifications propagate through every caller target in the
call-site relation until no access set changes. Procedure inputs and outputs
are then computed for classes retained by the existing threading policy.

## Failure Policy

SMACK aborts translation instead of continuing when:

- SeaDsa cannot compute a call-site mapping;
- SeaDsa returns a nonfunctional simulation relation that its public lookup API
  cannot enumerate;
- call-site region construction does not converge;
- a non-unique relation reaches a code path that requires one owner.

Global-rooted cells whose field-sensitive translation fails degrade to a
whole-node conservative region; cells not rooted at any global are anchored as
ordinary regions in the target context. Neither aborts translation.

These failures are preferable to proving a program against disconnected or
incomplete memory state.

## Regression Coverage

- `cs_dsa_region_threading.c`: nested heap and pointer flow across calls.
- `strings.c` and `strings1.c`: offset-preserving static-initializer mapping.
- `svcomp_private_maps.c`: private regions become procedure-local maps under
  `--local-private-memory-maps`, with a checked (non-vacuous) assertion.
- `static_init_dead_maps.c`: unused initializer field maps are eliminated.
- `init_func_locals.c`: init-function bodies using non-global-rooted memory.
- `deep_call_chain.c`: call-site mapping convergence beyond 100 passes.

## Main Files

| File | Responsibility |
|------|----------------|
| `DSAWrapper.h/cpp` | Function graph lookup and exact global-cell translation |
| `Regions.h/cpp` | Regions, relational mappings, merge repair, and backing classes |
| `SmackRep.cpp` | Resolve local indices and validate threaded mappings |

# Context-Sensitive DSA Memory Regions in SMACK

## Overview

SMACK runs SeaDsa in context-sensitive mode (`-sea-dsa=cs`) and constructs a
region vector for each LLVM function. Region indices are local to a function;
they are never compared across functions without a SeaDsa mapping.

The existing `cs` branch uses a hybrid backing policy. Entry-function regions
and larger cross-function classes use module-level maps, while selected small
classes are threaded through procedure inputs and outputs. The soundness fixes
below preserve that policy and its map declarations.

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
uses a whole-node bytewise region in the entry graph.

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
can create or merge caller regions. Failure to converge after 100 passes aborts
translation.

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
relations. The branch's existing backing policy is retained:

- entry regions keep their module-level declarations;
- small classes with two same-function regions and at most eight members can
  remain threaded through procedure interfaces;
- other cross-function classes use entry-owned or shared module-level maps;
- accessed regions outside mapped classes use the existing shared-map
  fallback.

Classes containing a non-unique relation are excluded from threading. If a
non-threaded class contains several regions from one function, selecting one
of them as its owner would disconnect the others, so that class uses one shared
map. This is a representational soundness requirement, not a memory-splitting
or map-count optimization.

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
- a required global cell cannot be translated or conservatively represented;
- a non-unique relation reaches a code path that requires one owner.

These failures are preferable to proving a program against disconnected or
incomplete memory state.

## Regression Coverage

- `cs_dsa_region_threading.c`: nested heap and pointer flow across calls.
- `strings.c` and `strings1.c`: offset-preserving static-initializer mapping.

## Main Files

| File | Responsibility |
|------|----------------|
| `DSAWrapper.h/cpp` | Function graph lookup and exact global-cell translation |
| `Regions.h/cpp` | Regions, relational mappings, merge repair, and backing classes |
| `SmackRep.cpp` | Resolve local indices and validate threaded mappings |

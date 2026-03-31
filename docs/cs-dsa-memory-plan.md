# Context-Sensitive DSA Memory Regions in SMACK

## Overview

SMACK uses **context-sensitive** sea-dsa analysis (`-sea-dsa=cs`) with **per-function memory regions**. Each function gets its own region vector computed from its CS graph, and memory maps are threaded through procedure signatures as parameters (reads) and returns (writes).

```boogie
// Memory maps are local in/out parameters, not globals
procedure foo(x: ref, $M.0.in: [ref]i8) returns ($M.0.out: [ref]i8)
{ var $M.0: [ref]i8;
  $M.0 := $M.0.in;
  $M.0 := $store.i8($M.0, x, 42);
  $M.0.out := $M.0; }

procedure main()
  modifies $M.0;
{ call $M.0 := foo(x, $M.0); }
```

Entry points (`main`) keep globals with `modifies` clauses. Non-entry procedures use local in/out parameters.

---

## Architecture

### Phase 1: Per-Function Region Construction

**Files:** `Regions.cpp` (runOnModule)

Each function's region vector is built from:
1. **Formal pointer parameters** -- `idx(&formalArg, &F)`
2. **Instructions** -- load/store/atomic/memcpy pointer operands via `visit(F)`
3. **Call-site actual pointer arguments** -- `idx(actualArg, &F)` for each call in the function
4. **Globals** -- `idx(&GV, &F)` for globals present in the function's DSA graph
5. **Pointer-returning calls** -- `idx(&callInst, &F)` for calls that return pointers (both declarations and definitions)
6. **Link-following** -- for each existing region, follow DSA pointer links to discover reachable nodes and create regions for them using `Region(Node*, ctx)`. This ensures callers have regions for data accessible through pointer indirection (e.g., `**arg`).

The `Region(Node*, LLVMContext&)` constructor creates a region directly from a DSA node without needing a Value*. This is needed because callers may not have LLVM values for data they never directly access but their callees do.

### Phase 2: Read/Write Sets

Direct memory accesses in each function are recorded:
- `LoadInst` -> readRegions
- `StoreInst` -> modifiedRegions
- `AtomicCmpXchgInst`, `AtomicRMWInst` -> both
- `MemSetInst` -> modifiedRegions
- `MemTransferInst` -> readRegions (source) + modifiedRegions (dest)

### Phase 2.5: Global Memory Mappings

For non-entry `usesGlobalMemory` functions (e.g., `__SMACK_static_init`), compute mappings from their region indices to the entry function's indices via shared globals.

### Phase 3: Call-Site Mappings

**`computeOneCallSiteMapping(CI, caller, callee)`** builds a map from callee region indices to caller region indices through:

1. **Parameter pairs** -- formal pointer params mapped to actual args
2. **Return value** -- callee's return value region mapped to caller's call result region
3. **Global pairs** -- shared globals (parameter mappings take priority over globals to preserve call-site specificity)
4. **Rep-matching extension** -- unmapped callee regions whose DSA node matches a mapped callee region's node
5. **DSA link-following** -- traverse pointer edges in both callee and caller DSA graphs to discover node correspondences for heap structures reachable through globals/parameters. Creates missing caller regions via `Region(Node*, ctx)` when needed.

**Conflict detection:** When a callee DSA node maps to multiple different caller nodes (e.g., two globals unified in the callee), it's marked as conflicting and excluded from link-following to avoid incorrect merging.

**Iteration:** `computeCallSiteMappings` runs iteratively (up to 10 passes) because link-following may create new regions in callers, which then need mappings computed for their own callers.

### Phase 3.5: Region Merge Propagation

**`propagateRegionMerges(M)`** enforces the soundness invariant: **regions must not alias**. Uses SCCs for proper ordering.

**Top-down pass:** When a caller maps two callee regions to the same caller region, the callee regions are merged (they alias from the caller's perspective). `mergeCalleeRegion` handles the merge and updates all affected call-site mappings.

**Bottom-up pass:** When a callee has collapsed regions that the caller keeps separate, the caller's regions are merged to match.

**Key invariant in `mergeCalleeRegion`:** When shifting callee-side keys in call-site mappings, existing entries (typically from parameter mappings) take priority over entries from merged-away regions. This prevents global mapping collisions from overwriting call-site-specific parameter mappings.

### Phase 4: Transitive Closure

**`computeFunctionRegions(M)`** propagates callee region accesses to callers through call-site mappings until convergence. Only mapped regions are propagated.

---

## Key Design Decisions

### Parameter Mapping Priority
Global pairs must not overwrite parameter pairs in the mapping (`!mapping.count(calleeR)` guard). Parameter mappings are call-site-specific and more precise. Without this, functions called with different global arguments (e.g., `acquire_lock(&main_lock)` vs `acquire_lock(&global_lock)`) would get incorrect mappings.

### DSA Link-Following
DSA graphs encode pointer relationships (e.g., `head` global links to the list struct node). The link-following extension traverses these edges to discover that nodes reachable through globals/parameters in the callee correspond to specific nodes in the caller. Without this, heap structures like linked lists would have incomplete mappings.

### Region Creation from DSA Nodes
The `Region(const seadsa::Node*, LLVMContext&)` constructor enables creating regions for DSA nodes that have no corresponding LLVM Value in the function. This is needed when:
- A caller passes a pointer and the callee accesses through multiple levels of indirection
- Phase 1 link-following discovers reachable nodes
- Phase 3 link-following creates regions during mapping computation

### Return Value Mapping
Call-site mappings include the callee's return value (matched via the callee's `ReturnInst` and the caller's `CallInst`). This is critical for function pointer dispatch patterns like `devirtbounce`, where data flows through return values rather than parameters.

---

## Test Results

**197 total tests, 195 passed, 0 failed, 2 unknown.**

The 2 unknowns (`smack_code_call`, `smack_code_call_fail`) use `__SMACK_code` to emit inline BPL calls that bypass the memory map threading. This is a pre-existing limitation of inline BPL with per-function memory maps.

---

## File Summary

| File | Change |
|------|--------|
| `DSAWrapper.h/cpp` | Function-aware `getNode`/`getOffset`/`isTypeSafe` with per-function graph lookup |
| `Regions.h/cpp` | Per-function region vectors, call-site mappings, link-following, merge propagation, `Region(Node*)` constructor |
| `SmackRep.h/cpp` | Memory map params/returns in procedure signatures, call-site mapping for threading |
| `SmackInstGenerator.cpp` | Prologue/epilogue for local memory shadows, entry block initialization |
| `SmackModuleGenerator.cpp` | Local var declarations for non-entry functions, global-scope region handling |
| `Prelude.cpp` | Per-function region types in prelude generation |
| `SmackOptions.h/cpp` | `usesGlobalMemory`, `isEntryPoint` helpers |
| `top.py` | Switch to `-sea-dsa=cs`, fix `VProperty.__members__` for `--check` flag |

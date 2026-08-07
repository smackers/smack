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

1. Build the authoritative SeaDsa call-site simulation with `Graph::computeCalleeCallerMapping`.
2. For each callee region, ask the `SimulationMapper` for the corresponding caller `Cell`.
3. Translate the mapped caller `Cell` back into the caller's local region index, creating a caller region if the caller has no LLVM `Value*` for that reachable node.

SMACK does not reimplement SeaDsa's mapping rules. SeaDsa owns the root matching for globals, return values, and pointer formal/actual pairs, plus recursive link following with offset/collapsed-node handling. If SeaDsa cannot map the call site, the translation fails instead of falling back to equal numeric region indices.

**Iteration:** `computeCallSiteMappings` runs iteratively (up to 10 passes) because link-following may create new regions in callers, which then need mappings computed for their own callers.

### Phase 3.5: Region Merge Propagation

**`propagateRegionMerges(M)`** enforces the soundness invariant: **regions must not alias**. Uses SCCs for proper ordering.

**Top-down pass:** When a caller maps two callee regions to the same caller region, the callee regions are merged (they alias from the caller's perspective). `mergeCalleeRegion` handles the merge and updates all affected call-site mappings.

**Bottom-up pass:** When a callee has collapsed regions that the caller keeps separate, the caller's regions are merged to match.

**Key invariant in `mergeCalleeRegion`:** When shifting callee-side keys in call-site mappings, existing entries (typically from parameter mappings) take priority over entries from merged-away regions. This prevents global mapping collisions from overwriting call-site-specific parameter mappings.

### Phase 4: Transitive Closure

**`computeFunctionRegions(M)`** propagates callee region accesses to callers through call-site mappings until convergence. Only mapped regions are propagated.

### Phase 5: Procedure Memory Interfaces

**`computeInterfaceRegions(M)`** separates local memory from caller-visible memory:

1. **Input regions** are accessed regions reachable from formal pointer parameters or globals.
2. **Output regions** are modified regions reachable from formal pointer parameters, globals, or the function return cell.

Only input regions become `$M.r.in` parameters, and only output regions become `$M.r.out` returns. Private stack/heap regions remain local Boogie variables; they are not threaded through callers.

---

## Key Design Decisions

### SeaDsa-Owned Mapping
The call-site mapping must follow SeaDsa's `SimulationMapper`; function-local region numbers are not comparable across functions. Falling back from an unmapped callee region to the same numeric caller region is unsound and is intentionally rejected.

### Interface Reachability
DSA graphs encode which nodes are reachable from parameters, globals, and return values. Procedure signatures expose only those regions. This avoids requiring callers to provide memory maps for callee-private allocas or heap objects that do not escape.

### Region Creation from DSA Nodes
The `Region(const seadsa::Node*, LLVMContext&)` constructor enables creating regions for DSA nodes that have no corresponding LLVM Value in the function. This is needed when:
- A caller passes a pointer and the callee accesses through multiple levels of indirection
- Phase 1 link-following discovers reachable nodes
- Phase 3 link-following creates regions during mapping computation

### Return Value Mapping
Call-site mappings include the callee's SeaDsa return cell and the caller's call-result cell. This is critical for function pointer dispatch patterns like `devirtbounce`, where data flows through return values rather than parameters.

---

## Test Notes

The `smack_code_call` tests use `__SMACK_code` to emit inline BPL calls that bypass the memory map threading. This is a pre-existing limitation of inline BPL with per-function memory maps.

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

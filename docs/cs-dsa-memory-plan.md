# Plan: Context-Sensitive DSA Memory Regions in SMACK

## Context

SMACK currently uses **context-insensitive** sea-dsa analysis (`-sea-dsa=ci`), producing a single global points-to graph for the entire module. All memory regions (`$M.0`, `$M.1`, ...) are declared as **global Boogie variables**, and every procedure implicitly accesses all of them. This means Corral must conservatively havoc all memory regions at each unresolved call site, limiting verification scalability.

The goal is to switch to **context-sensitive** sea-dsa (`-sea-dsa=cs` or `-sea-dsa=butd-cs`) so each function has its own DSA graph. This enables computing per-function read/write region sets, and threading only the relevant regions through procedure signatures as parameters (reads) and returns (writes).

**Target Boogie transformation:**
```boogie
// BEFORE (global memory)
var $M.0: [ref]i8;
var $M.1: [ref]i32;

procedure foo(x: ref)
  modifies $M.0;
{ $M.0 := $store.i8($M.0, x, 42); }

// AFTER (region-parameterized)
procedure foo(x: ref, $M.0: [ref]i8) returns ($M.0: [ref]i8)
{ $M.0 := $store.i8($M.0, x, 42); }

procedure main()
  modifies $M.0, $M.1;
{ call $M.0 := foo(x, $M.0); }
```

Non-entry procedures use their regions as **local** in/out parameters. Entry points (`main`) keep using globals with `modifies` clauses. The procedure body code (`$load`/`$store` referencing `$M.R`) does not change -- the trick is that `$M.R` becomes a local variable shadowing the global.

---

## Implementation Steps

### Step 1: DSAWrapper -- Support Context-Sensitive Analysis

**Files:** `lib/smack/DSAWrapper.cpp`, `include/smack/DSAWrapper.h`

1a. **Remove the CI assertion** (line 33-34 of DSAWrapper.cpp):
```cpp
// Remove:
assert(SD->kind() == seadsa::GlobalAnalysisKind::CONTEXT_INSENSITIVE && ...);
```

1b. **Make `getNode`/`getOffset` function-aware.** Currently they query the single global graph `DG`. Change them to resolve the function from the value and query the per-function graph:
```cpp
const seadsa::Node *DSAWrapper::getNode(const Value *v) {
  auto &graph = getGraphForValue(v);
  if (!graph.hasCell(*v)) return nullptr;
  return graph.getCell(*v).getNode();
}

seadsa::Graph &DSAWrapper::getGraphForValue(const Value *v) {
  if (auto *I = dyn_cast<Instruction>(v))
    return SD->getGraph(*I->getParent()->getParent());
  if (auto *A = dyn_cast<Argument>(v))
    return SD->getGraph(*A->getParent());
  // For globals/constants, use fallback graph
  return *DG;
}
```

Keep `DG` as a fallback for globals: `DG = &SD->getGraph(*M.begin())` still works (the entry function's graph contains global info).

1c. **Expose per-function graph access** for the Regions pass:
```cpp
seadsa::Graph &getGraph(const llvm::Function &F) { return SD->getGraph(F); }
bool hasGraph(const llvm::Function &F) const { return SD->hasGraph(F); }
```

1d. **Update `collectStaticInits` and `countGlobalRefs`** to handle multiple graphs. Currently these iterate `DG` which is the single graph. With CS mode, iterate all functions' graphs and union results. The simplest approach: keep using `DG` (entry function graph) since globals appear in the entry function's graph in CS mode too.

---

### Step 2: Regions -- Per-Function Read/Write Region Sets

**Files:** `lib/smack/Regions.cpp`, `include/smack/Regions.h`

2a. **Add per-function region tracking** to the `Regions` class:
```cpp
// In Regions.h:
struct FunctionRegionInfo {
  std::set<unsigned> readRegions;
  std::set<unsigned> modifiedRegions;
};
std::map<const llvm::Function*, FunctionRegionInfo> funcRegions;

// Public API:
const std::set<unsigned>& getReadRegions(const llvm::Function *F) const;
const std::set<unsigned>& getModifiedRegions(const llvm::Function *F) const;
std::set<unsigned> getAccessedRegions(const llvm::Function *F) const;
```

2b. **Compute per-function region sets** after the global `visit(M)` pass in `runOnModule`. Two approaches:

**Option A (instruction-based):** Iterate each function's instructions, call `idx(ptr_operand)` for each load/store/atomic/memcpy/memset, and classify as read or modified:
```cpp
for (auto &F : M) {
  if (F.isDeclaration()) continue;
  for (auto &BB : F) {
    for (auto &I : BB) {
      if (auto *LI = dyn_cast<LoadInst>(&I)) {
        unsigned r = idx(LI->getPointerOperand());
        funcRegions[&F].readRegions.insert(r);
      } else if (auto *SI = dyn_cast<StoreInst>(&I)) {
        unsigned r = idx(SI->getPointerOperand());
        funcRegions[&F].modifiedRegions.insert(r);
      }
      // ... atomics, memcpy, memset ...
    }
  }
}
```

**Option B (DSA-graph-based):** For each function, iterate its DSA graph nodes, match nodes to global regions by representative, classify by `node->isRead()`/`node->isModified()`. This automatically includes transitive effects (callees), since the CS graph propagates callee effects.

**Recommendation:** Use Option A for the direct region mapping (it reuses existing `idx()` logic), then **add transitive closure** by iterating call instructions and unioning callee region sets (post-order on call graph).

---

### Step 3: SmackRep -- Procedure Signatures with Memory Parameters

**Files:** `lib/smack/SmackRep.cpp`, `include/smack/SmackRep.h`

3a. **Modify `procedure(Function*, CallInst*)`** (line 1037) to add memory region params/returns for non-entry-point procedures:

```cpp
// After existing param computation (line 1044-1045):
if (!SmackOptions::isEntryPoint(F->getName()) && !F->isDeclaration()) {
  auto accessed = regions->getAccessedRegions(F);
  for (unsigned r : accessed)
    params.push_back({memReg(r), memType(r)});  // $M.R as input param

  auto modified = regions->getModifiedRegions(F);
  for (unsigned r : modified)
    rets.push_back({memReg(r), memType(r)});    // $M.R as output return
}
```

Note: We use the same name `$M.R` for both param and return, relying on Boogie's scoping (input params and output returns are distinct). Actually, Boogie requires distinct names, so use `$M.R` for input and a differently-scoped return. In Boogie, `returns (x: T)` creates a local `x` that is assigned and returned. So the pattern is:

```boogie
procedure foo(x: ref, $M.0: [ref]i8) returns (ret: i32, $M.0: [ref]i8)
```

Wait -- Boogie does NOT allow the same name for both an input param and an output return. So we need either:
- Use `$M.R` as input param, and a different name like `$M.R.out` for return, with an epilogue copy
- Use `$M.R` as a local variable, `$M.R.in` as input param, `$M.R.out` as output return, with prologue/epilogue copies

**Recommended approach (local shadow):**
- Input params: `$M.R.in`
- Output returns: `$M.R.out`
- Local variable: `$M.R` (declared as local, initialized from `$M.R.in` at entry, copied to `$M.R.out` at returns)
- Procedure body code continues to reference `$M.R` unchanged

```cpp
if (!isEntryPoint && !F->isDeclaration()) {
  auto accessed = regions->getAccessedRegions(F);
  for (unsigned r : accessed)
    params.push_back({memReg(r) + ".in", memType(r)});

  auto modified = regions->getModifiedRegions(F);
  for (unsigned r : modified)
    rets.push_back({memReg(r) + ".out", memType(r)});
}
```

3b. **Modify `call(Function*, User&)`** (line 1122) to pass and receive memory regions:

```cpp
// After existing arg computation:
if (!SmackOptions::isEntryPoint(f->getName())) {
  auto accessed = regions->getAccessedRegions(f);
  for (unsigned r : accessed)
    args.push_back(Expr::id(memPath(r)));  // pass current $M.R

  auto modified = regions->getModifiedRegions(f);
  for (unsigned r : modified)
    rets.push_back(memPath(r));            // assign returned $M.R
}
```

3c. **Handle declared (external) functions conservatively.** For functions with no body, assume they may access/modify all regions. Add a helper:
```cpp
bool isConservativeFunction(Function *F) {
  return F->isDeclaration() && !isSpecialFunction(F);
}
```

---

### Step 4: SmackInstGenerator -- Prologue/Epilogue for Local Memory Shadows

**Files:** `lib/smack/SmackInstGenerator.cpp`

4a. **Patch `visitReturnInst`** (line 240) to copy local memory to output params before returning:

```cpp
void SmackInstGenerator::visitReturnInst(llvm::ReturnInst &ri) {
  processInstruction(ri);
  llvm::Value *v = ri.getReturnValue();
  if (v)
    emit(Stmt::assign(Expr::id(Naming::RET_VAR), rep->expr(v)));

  // Copy modified regions to output params
  const Function *F = ri.getParent()->getParent();
  if (!SmackOptions::isEntryPoint(F->getName())) {
    auto modified = rep->getRegions()->getModifiedRegions(F);
    for (unsigned r : modified)
      emit(Stmt::assign(Expr::id(rep->memReg(r) + ".out"),
                         Expr::id(rep->memReg(r))));
  }

  emit(Stmt::assign(Expr::id(Naming::EXN_VAR), Expr::lit(false)));
  emit(Stmt::return_());
}
```

4b. **Add prologue in entry block** to initialize local shadows from input params. In `SmackInstGenerator`, detect the entry block and emit initialization:

```cpp
// At the start of visiting the entry block:
if (&bb == &bb.getParent()->getEntryBlock()) {
  const Function *F = bb.getParent();
  if (!SmackOptions::isEntryPoint(F->getName())) {
    auto accessed = rep->getRegions()->getAccessedRegions(F);
    for (unsigned r : accessed)
      emit(Stmt::assign(Expr::id(rep->memReg(r)),
                         Expr::id(rep->memReg(r) + ".in")));
  }
}
```

---

### Step 5: SmackModuleGenerator -- Local Declarations and Entry-Point Modifies

**File:** `lib/smack/SmackModuleGenerator.cpp`

5a. **Add local variable declarations** for memory region shadows in non-entry procedures. After `igen.visit(F)` (line 80), add:

```cpp
if (!SmackOptions::isEntryPoint(F.getName())) {
  auto accessed = getAnalysis<Regions>().getAccessedRegions(&F);
  for (unsigned r : accessed)
    P->getDeclarations().push_back(
      Decl::variable(rep.memReg(r), rep.memType(r)));
}
```

5b. **Add modifies clauses for entry-point procedures** at line 94 (the `// MODIFIES` comment):

```cpp
if (SmackOptions::isEntryPoint(F.getName())) {
  auto modified = getAnalysis<Regions>().getModifiedRegions(&F);
  for (unsigned r : modified)
    for (auto P : procs)
      P->getModifies().push_back(rep.memReg(r));
}
```

---

### Step 6: top.py -- Switch DSA Mode

**File:** `share/smack/top.py`

6a. Change line 742 from `-sea-dsa=ci` to `-sea-dsa=cs` (or `butd-cs` for the most precise analysis).

6b. Optionally add a CLI flag `--context-sensitive-memory` to toggle between old (CI global) and new (CS parameterized) behavior, allowing fallback. Default: enabled.

---

### Step 7: Prelude -- No Changes Needed

Global `var $M.R: type;` declarations stay. They are used by entry-point procedures and serve as canonical storage. Non-entry procedures shadow them with locals.

---

## Edge Cases

| Case | Handling |
|------|----------|
| **Indirect calls** (unresolved function pointers) | Pass all regions conservatively (fallback) |
| **Recursive functions** | Sea-dsa CS handles recursion via fixpoint; signature is self-consistent |
| **External/declared functions** | Conservative: assume all regions accessed/modified |
| **Contract expressions** | Already pass all memory maps as params (line 1064-1066); no change needed initially |
| **memcpy/memset** | Already parameterized with memory in/out; called correctly via `SmackInstGenerator::visitMemCpyInst` which uses `rep->memReg(r)` (resolves to local shadow) |
| **Entry points** | Keep using global `$M.R` with `modifies` clauses; no params/returns for memory |
| **Functions accessing no memory** | Empty region sets; no extra params/returns added |

## Open Problem: Cross-Function Node Identity

### Problem Statement

Steps 1-6 were implemented and built successfully. Regression testing (regtest.py) showed **2 failures**: `two_arrays.c` and `two_arrays1.c` (151 passed, 16 failed, 30 unknown).

Root cause: `Region::overlaps` in Regions.cpp compares DSA node pointers (`representative == R.representative`). With CS-DSA, each function has its own graph with its own node objects. Two functions accessing the same logical memory get different `seadsa::Node*` pointers, so their regions don't merge.

**Concrete example:** In `two_arrays.c`, `resetArray(int *array)` and `setArray(int *array)` both write through a pointer parameter. With CS-DSA:
- `resetArray`'s `array` parameter → node in `resetArray`'s graph → `$M.0`
- `setArray`'s `array` parameter → node in `setArray`'s graph → `$M.1`
- `main`'s `arrayOne`/`arrayTwo` → node in `main`'s graph → mapped to one of these

Result: `main` calls `call $M.0 := resetArray(ptr, $M.0)` and `call $M.1 := setArray(ptr, $M.1)`, treating them as separate regions. But they're the same heap memory — `setArray`'s writes don't show up when `main` reads `$M.0`.

### Candidate Solutions

**Option A: SimulationMapper-based node canonicalization**
- Sea-dsa provides `SimulationMapper` for computing callee→caller node mappings at call sites
- For each function, map its nodes to the caller's (or entry point's) canonical nodes
- Use the canonical node as `Region::representative`
- Pros: fully leverages CS-DSA precision
- Cons: complex implementation; need to handle the full call graph

**Option B: Entry-point graph as canonical source**
- Use the entry function's (main) DSA graph for all region computation
- The entry function's graph sees all memory (after bottom-up + top-down propagation in `butd-cs` mode)
- For helper functions, look up their parameter nodes in the caller's graph context
- Pros: simpler — one canonical graph
- Cons: requires `butd-cs` (not just `cs`) for full top-down propagation; still need mapping for function-local values

**Option C: Separate region identity from access tracking**
- Use CI analysis for region identity (determining which `$M.R` a pointer belongs to) — this is what the current `visit(M)` + `idx()` path already does
- Use CS analysis only for per-function read/write tracking (which global regions a function touches)
- The per-function tracking would query the CS graph's nodes, then map them back to CI regions
- Pros: minimal change to existing region computation; clean separation
- Cons: running two DSA analyses (CI + CS) may be costly; or must find another way to map CS nodes to CI regions

**Option D: Node identity via allocation sites or types**
- Instead of comparing node pointers, identify nodes by their allocation sites or structural properties
- Sea-dsa nodes have `getAllocSites()` — if two nodes share allocation sites, they represent overlapping memory
- Pros: works across function boundaries without explicit mapping
- Cons: allocation sites may not be available for all nodes (e.g., parameters); may over-merge

### Decision Needed

Which approach to pursue? The choice affects:
- Whether we use `-sea-dsa=cs` or `-sea-dsa=butd-cs`
- Whether we need dual CI+CS analysis
- How `Region::overlaps` or `Region::init` must change
- Complexity of the implementation

## Verification Plan

1. **Build:** `cd /home/shaobo/smack-project/smack/build && make -j8`
2. **Unit test:** Run existing SMACK regression tests: `make test` (or `lit test/`)
3. **Inspect output:** Run SMACK on a simple test case and inspect the `.bpl` file to verify procedure signatures have memory params/returns, and call sites thread them correctly
4. **AWS benchmarks:** Run `aws.xml` benchmark and compare false alarm counts / correctness against the baseline
5. **DD benchmarks:** Run `dd.xml` and compare verification performance (should improve with tighter modifies sets)

## Critical Files Summary

| File | Change |
|------|--------|
| `lib/smack/DSAWrapper.cpp` | Function-aware `getNode`/`getOffset`, remove CI assertion |
| `include/smack/DSAWrapper.h` | Add `getGraph(F)`, `getGraphForValue(v)` |
| `lib/smack/Regions.cpp` | Compute per-function read/modified region sets |
| `include/smack/Regions.h` | Add `FunctionRegionInfo`, query API |
| `lib/smack/SmackRep.cpp` | Add memory params/returns to `procedure()`, thread in `call()` |
| `lib/smack/SmackInstGenerator.cpp` | Prologue/epilogue for local memory shadows |
| `lib/smack/SmackModuleGenerator.cpp` | Local decls, entry-point modifies clauses |
| `share/smack/top.py` | Switch `-sea-dsa=ci` to `-sea-dsa=cs` |

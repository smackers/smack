# Sign Analysis Pass for SMACK

## Context

LLVM IR integers are signless — the sign is encoded per-operation (e.g., `sdiv` vs `udiv`), not per-value. For downstream translation (e.g., to Boogie or other typed IRs), it's useful to infer whether a given SSA value is "intended" to be signed or unsigned. This pass performs a best-effort dataflow analysis to recover that intent.

## Frontend sign evidence

Clang normally preserves signed no-wrap intent with `nsw`, but unsigned
wrapping arithmetic often has no corresponding `nuw` flag. To retain both
kinds of source-level intent, SMACK compiles user C-family translation units
with Clang's `signed-integer-overflow` and `unsigned-integer-overflow`
sanitizers. The resulting `llvm.*with.overflow` intrinsics are used only as an
encoding of signedness.

An early `IntegerOverflowChecker` pass recognizes frontend-generated
intrinsics by their `!nosanitize` metadata, replaces them with ordinary
same-width arithmetic carrying `!overflow.sign`, folds away the UBSan guard,
and removes the now-unreachable handler. `SignAnalysis` consumes that inert
metadata. This path neither emits `__SMACK_check_overflow` calls nor preserves
runtime overflow checks.

SMACK library and model sources are deliberately compiled without these
sanitizer flags. Genuine checked-arithmetic intrinsics (for example, those
emitted by Rust) and the explicit `--check integer-overflow` mode retain their
existing checking behavior.

## Core Algorithm

### 1. Sign Lattice

```
       Unknown      (top — no evidence yet)
       /     \
   Signed   Unsigned
       \     /
       Conflict     (bottom — contradictory evidence)
```

**Meet operator:** `meet(a, b)` = `a` if `a == b`; return whichever is non-Unknown; otherwise `Conflict`.

### 2. Single Domain

The analysis tracks signs in a single map:

- **SSA map** (`SignMap`): maps `const Value*` → `Sign` for all SSA values, including load results.

Memory propagation (§4) connects loads and stores via DSA alias queries, but the results are stored in the same `SignMap` — there is no separate memory map.

### 3. Constraint Sources

Every integer instruction is classified into one of three categories:

#### A. Instructions that constrain their **operands** (backward)

| Instruction / Predicate | Operand sign |
|--------------------------|--------------|
| `sdiv`, `srem`, `ashr` | `Signed` |
| `sext` (source operand) | `Signed` |
| `icmp slt/sgt/sle/sge` | `Signed` |
| `udiv`, `urem`, `lshr` | `Unsigned` |
| `zext` (source operand) | `Unsigned` |
| `icmp ult/ugt/ule/uge` | `Unsigned` |

#### B. Instructions that constrain their **result** (forward)

| Instruction | Result sign |
|-------------|-------------|
| `sext` | `Signed` |
| `zext` | `Unsigned` |
| `fptoui` | `Unsigned` |
| `fptosi` | `Signed` |

#### C. Sign-agnostic instructions (no constraint by default)

`add`, `sub`, `mul`, `shl`, `and`, `or`, `xor`, `icmp eq/ne`, `trunc`, `select`

**However**, `!overflow.sign` metadata produced from frontend overflow
intrinsics and `nsw`/`nuw` flags on sign-agnostic arithmetic provide direct
evidence:

- `!overflow.sign !{!"s"}` → operands and result are `Signed`
- `!overflow.sign !{!"u"}` → operands and result are `Unsigned`
- `add nsw` / `sub nsw` / `mul nsw` / `shl nsw` → operands and result are `Signed`
- `add nuw` / `sub nuw` / `mul nuw` / `shl nuw` → operands and result are `Unsigned`
- If both flags are present, we do not constrain (they don't conflict in LLVM semantics, but for sign inference they're ambiguous).

### 4. Memory Propagation (via sea-dsa)

Sign information flows through memory by connecting loads to aliasing stores (and vice versa) using `DSAWrapper`. Everything stays in the single `SignMap`.

#### Alias resolution

Two pointers alias if they map to the same abstract memory cell. A cell is identified by `(DSNode*, offset)`, obtained via `DSAWrapper::getNode(ptr)` and `DSAWrapper::getOffset(ptr)`.

Edge cases (learned from `Regions.cpp`):
- **Collapsed nodes** (`node->isOffsetCollapsed()`): all offsets within the node alias each other. Normalize offset to 0 for these nodes.
- **Incomplete/complicated nodes** (`node->isIncomplete()`, `node->isExternal()`, `node->isIntToPtr()`, etc.): conservatively alias other nodes of the same kind. Skip sign propagation for these — leave loaded values as `Unknown`.
- **Null nodes**: `getNode()` returns `nullptr` for values without cells (e.g., `undef`). Skip.

#### Load: aliasing stores → load result

```
%y = load i32, i32* %p
```
- Use DSA to find all `store` instructions whose pointer aliases `%p` (same cell).
- `sign(%y) = meet(sign(%y), sign(stored_value))` for each aliasing store.

#### Store: stored value → aliasing load results

```
store i32 %x, i32* %p
```
- Use DSA to find all `load` instructions whose pointer aliases `%p`.
- `sign(load_result) = meet(sign(load_result), sign(%x))` for each aliasing load.

#### Implementation

During initialization, build an index of stores and loads per cell:
- `CellStores`: maps `(DSNode*, offset)` → list of stored `Value*`
- `CellLoads`: maps `(DSNode*, offset)` → list of load result `Value*`

For collapsed nodes, the offset in the key is normalized to 0 so all accesses to the same collapsed node are grouped together. Incomplete/complicated nodes are excluded from the index.

During propagation, when a store's value sign changes, propagate to all loads in the same cell, and vice versa.

#### memcpy / memmove

- Resolve source and destination pointers to their DSNodes.
- For each aliasing store to the source, propagate to loads from the destination.
- If the copy size or field layout is unknown, conservatively skip.

#### memset

- Typically zeroing memory — zero is both signed and unsigned, so no sign constraint. Skip.

#### Soundness

sea-dsa over-approximates the set of memory locations a pointer can refer to. Since we use `meet` (which can only move values downward in the lattice), this is conservative: aliased stores from different sign contexts will produce `Conflict`, which is correct.

### 5. Propagation Rules

#### Forward propagation (def → result)
For each instruction `I` producing value `V`:
- If `I` is in category B, set `sign(V) = meet(sign(V), <table value>)`.
- If `I` has signed `!overflow.sign` metadata or `nsw` (only) → `sign(V) = meet(sign(V), Signed)`.
- If `I` has unsigned `!overflow.sign` metadata or `nuw` (only) → `sign(V) = meet(sign(V), Unsigned)`.
- If `I` is a `PHINode`: `sign(V) = meet over all incoming values`.
- If `I` is a `select`: `sign(V) = meet(sign(true_val), sign(false_val))`.
- If `I` is a `trunc`: `sign(V) = sign(source operand)` (propagate through).
- If `I` is a `load`: meet signs of all aliasing stores' values into `sign(I)` (see §4).

#### Backward propagation (use → operands)
For each instruction `I` using value `V` as an operand:
- If `I` is in category A, update `sign(V) = meet(sign(V), <table value>)`.
- If `I` has signed `!overflow.sign` metadata or `nsw` (only) → `sign(V) = meet(sign(V), Signed)` for each integer operand.
- If `I` has unsigned `!overflow.sign` metadata or `nuw` (only) → `sign(V) = meet(sign(V), Unsigned)` for each integer operand.
- If `I` is a `store`: meet `sign(stored_value)` into all aliasing load results (see §4).

### 6. Initialization

Before iteration:
- Run `DSAWrapper` to build alias information.
- Build the `CellStores` and `CellLoads` indices by scanning all load/store instructions.
- Scan all instructions once. For each instruction, apply forward and backward rules (including load/store memory rules) to seed `SignMap`.
- Constants: leave as `Unknown` (their sign is determined by how they're used).

### 7. Interprocedural Propagation

Sign information crosses function boundaries in two ways:

- **Memory**: already handled by DSA (module-wide, context-insensitive).
- **Call/return**: at a `CallInst`, propagate signs between actual arguments and formal parameters, and between the callee's return value and the `CallInst` result.

#### Forward (caller → callee)
- At a `CallInst`, propagate `sign(actual_arg)` → `sign(formal_param)` for each argument.

#### Backward (callee → caller)
- At a `ReturnInst`, propagate `sign(return_value)` → `sign(CallInst result)` for all call sites.
- At a `CallInst`, propagate `sign(formal_param)` → `sign(actual_arg)` for each argument.

### 8. Fixpoint Iteration

```
repeat:
  changed = false
  for each function F in module:
    for each instruction I in F:
      changed |= propagateForward(I)   // includes load, call → callee
      changed |= propagateBackward(I)  // includes store, return → caller
until !changed
```

The lattice has height 3 (Unknown → Signed/Unsigned → Conflict) and values can only move downward, so this terminates in at most 3 passes over the module (in practice, 2).

> **TODO**: The current implementation uses a simple global fixpoint over all functions in arbitrary order. For large modules with deep call chains, this could be improved by using bottom-up/top-down traversal of the call graph with SCC-based handling of recursive functions. The simple approach is correct (same lattice, same monotone transfer functions) but may require more iterations.

### 8. Query Interface

```cpp
Sign getSign(const Value *V) const;
```

Returns the inferred sign. Values not in the map default to `Unknown`.

### 9. Debug Support

A `dump()` method prints the sign map to `errs()`, showing each value and its inferred sign. Gated behind `DEBUG_TYPE "smack-sign"` so it only appears with `-debug-only=smack-sign`.

## Implementation Structure

```cpp
// SignAnalysis.h
enum class Sign { Unknown, Signed, Unsigned, Conflict };
Sign meetSign(Sign a, Sign b);

using MemCell = std::pair<const sea_dsa::Node *, unsigned>;

class SignAnalysis : public llvm::ModulePass {
  static char ID;
  std::map<const Value*, Sign> SignMap;

  // Indices connecting loads and stores through DSA alias cells
  std::map<MemCell, std::vector<const Value*>> CellStores;  // cell → stored values
  std::map<MemCell, std::vector<const Value*>> CellLoads;   // cell → load results

  DSAWrapper *DSA = nullptr;

  bool update(const Value *V, Sign S);       // meet into sign map
  MemCell resolvePointer(const Value *Ptr);   // pointer → (DSNode, offset)

  void buildMemoryIndex(Module &M);          // build CellStores/CellLoads
  void initialize(Module &M);
  bool propagate(Module &M);
  bool propagateForward(Instruction &I);
  bool propagateBackward(Instruction &I);

public:
  void getAnalysisUsage(AnalysisUsage &AU) const override;
  bool runOnModule(Module &M) override;
  Sign getSign(const Value *V) const;
  Sign getConstantOperandSign(const User *U) const;
  void dump() const;
};
```

## Integration with SmackRep (constant rendering)

`SmackRep` uses `SignAnalysis` first and retains its local heuristic as a
fallback when the result is `Unknown` or `Conflict`.

Integer constants are deliberately absent from `SignMap`. LLVM uniques a
`ConstantInt` by context, type, and bit pattern, so the same object can be used
as signed in one expression and unsigned in another. Recording either sign on
the constant would leak that decision between unrelated uses.

Instead, `SmackRep::expr()` threads the surrounding `User` to `lit()`, which
queries `SignAnalysis::getConstantOperandSign()`. That method uses the user's
inferred sign, or the meet of its non-constant integer operands. Explicitly
unsigned operations such as `udiv`, `urem`, unsigned comparisons, and select
conditions remain authoritative at the individual use.

If the per-use result is `Signed`, negative constants are rendered as
`$sub.iN(0, abs)`. If it is `Unsigned`, they are rendered as their positive
bit-pattern value. `Unknown` and `Conflict` use the previous two-flag heuristic.

### Wiring

- `SmackModuleGenerator::getAnalysisUsage()` adds `AU.addRequired<SignAnalysis>()`.
- `SmackModuleGenerator::generateProgram()` passes `&getAnalysis<SignAnalysis>()` to `SmackRep` constructor.
- `SignAnalysis` is added to the pipeline in `llvm2bpl.cpp` (before `SmackModuleGenerator`).

### Files modified

| File | Changes |
|------|---------|
| `include/smack/SmackRep.h` | Add `SignAnalysis*` and thread an optional per-use `User` through expression rendering |
| `lib/smack/SmackRep.cpp` | Query the per-use sign before falling back to the existing literal heuristic |
| `include/smack/SmackModuleGenerator.h` | No change needed |
| `lib/smack/SmackModuleGenerator.cpp` | Add `SignAnalysis` to `getAnalysisUsage`, pass to `SmackRep` |
| `tools/llvm2bpl/llvm2bpl.cpp` | Add `SignAnalysis` pass to pipeline |

## Key Dependencies

- `DSAWrapper` (`include/smack/DSAWrapper.h`, `lib/smack/DSAWrapper.cpp`) — wraps sea-dsa's `GlobalAnalysis`, provides `getNode(const Value*)` and `getOffset(const Value*)` to resolve pointers to `(DSNode*, offset)` pairs.

## Verification

1. **Build**: add files to CMakeLists.txt, run `cmake --build`.
2. **Functional test**: write C test files where constants appear in signed/unsigned contexts, compile with SMACK, and use `@checkbpl grep` to assert the generated Boogie renders constants correctly (e.g., `-1` as `$sub.i32(0, 1)` in signed context, as `4294967295` in unsigned context).
3. **Regression**: run existing SMACK test suite (`test/regtest.py`) to ensure no existing tests break.

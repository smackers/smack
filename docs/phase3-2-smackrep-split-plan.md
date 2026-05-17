# Phase 3.2 — SmackRep god-class split plan

## Why

`lib/smack/SmackRep.cpp` is 2042 LOC; `include/smack/SmackRep.h` is 718 LOC
with 40+ public methods spanning four orthogonal concerns. Any change in
`SmackRep` triggers a rebuild of every translator file that includes the
header (20+ files). Reviewers can't isolate "this PR touches type
lowering" from "this PR touches contract handling" because they all live
together. Phase 3.1 already shipped — smart-pointer cleanups in
`SmackRep`/`Prelude`/`SimplifyLibCalls`/`SmackModuleGenerator`/`Contracts`
— so the file is stable enough to split now.

Goal: each new file ≤ 800 LOC; header pulled apart along seam lines that
the current code already follows by section comment.

## Proposed decomposition

Inspect `lib/smack/SmackRep.cpp` member-by-member. The 40+ methods cluster
into four groups, each already contiguous in the file:

| New file (lib/)         | New header (include/)     | Approx. LOC | Members moved |
|-------------------------|---------------------------|------------:|---------------|
| `SmackTypeRep.cpp`      | `SmackTypeRep.h`          |      ~400   | `type`, `pointerType`, `intType`, `vectorType`, `storageSize`, `offset`, `getElementSize`, `getIntSize`, `getSize`, `pointeeType`, helpers in the type-lowering header block |
| `SmackMemRep.cpp`       | `SmackMemRep.h`           |      ~800   | `memPath`, `load`/`store`, `ptrArith`, `mapSelExpr`, GEP traversal (`offset(ArrayType, idx)`, GEP-walk loops), memory region helpers that call `Regions`, `auxiliaryDeclarations` (memory section), `safeLoad`/`unsafeLoad`/`safeStore`/`unsafeStore` callees |
| `SmackExprRep.cpp`      | `SmackExprRep.h`          |      ~500   | `expr`, `lit`, `op`, `procName` overloads, function call lowering, vector op stitching, value-to-Boogie-expression conversion |
| `SmackContractRep.cpp`  | `SmackContractRep.h`      |      ~342   | `valueAnnotation` (already migrated to fatal-user-error in Phase 3.5), `returnValueAnnotation`, contract extraction helpers, init-func registration, modifies/oracleModifiesForFunction |
| `SmackRep.cpp` (facade) | `SmackRep.h` (facade)     |       ~50   | constructor, member storage, `globalDecl`, `procedure`, public surface delegating to the four sub-objects |

Naming: `SmackTypeRep` / `SmackMemRep` / `SmackExprRep` /
`SmackContractRep` mirror Prelude's `TypeDeclGen` / `MemDeclGen` /
`IntOpGen` / `PtrOpGen` / `FpOpGen` pattern that already shipped in
Phase 3.1.

## Class topology

Keep `SmackRep` as the public facade. The four sub-classes hold a
reference back to the facade so they can call each other through it:

```cpp
class SmackRep {
public:
  SmackRep(const llvm::DataLayout *dl, Naming *naming, Program *program,
           Regions *regions);

  // Public methods preserved verbatim — each is now a one-line forwarder
  // to typeRep/memRep/exprRep/contractRep. Source compatibility for
  // SmackInstGenerator, SmackModuleGenerator, Prelude, ExtractContracts.
  std::string type(const llvm::Type *t);
  const Expr *expr(const llvm::Value *v);
  const Expr *load(const llvm::Value *p, llvm::Type *t);
  const Stmt *valueAnnotation(const llvm::CallInst &CI);
  /* ...etc... */

private:
  // Shared state (preserve current member set).
  const llvm::DataLayout *DL;
  Naming *naming;
  Program *program;
  Regions *regions;
  std::list<const llvm::Function *> initFuncs;
  std::map<std::string, std::string> annotationPtrAliases;

  // Sub-objects. unique_ptr (Phase 3.1 pattern). Each holds SmackRep&.
  std::unique_ptr<SmackTypeRep>     typeRep;
  std::unique_ptr<SmackMemRep>      memRep;
  std::unique_ptr<SmackExprRep>     exprRep;
  std::unique_ptr<SmackContractRep> contractRep;
};
```

Each sub-class signature:

```cpp
class SmackTypeRep {
public:
  explicit SmackTypeRep(SmackRep &rep) : rep(rep) {}
  // (methods moved from SmackRep::type, intType, pointerType, ...)
private:
  SmackRep &rep;
};
```

This is the same shape `Prelude` already uses for its `Gen` sub-objects
(`include/smack/Prelude.h:187+`).

## Mechanical migration steps

Each step is a single PR. Each PR keeps the public API of `SmackRep`
identical; reviewers + CI compare regtest pass counts before/after.

1. **Carve out `SmackTypeRep`.** Type-related members are the most
   self-contained (no Regions/Program touches). Move
   declarations + definitions. Add a forward declaration in
   `SmackRep.h` and a `std::unique_ptr<SmackTypeRep>` member. Public
   `SmackRep::type(...)` etc. become one-line forwarders. ~400 LOC out.

2. **Carve out `SmackMemRep`.** Largest cut. Touches `Regions` heavily;
   verify the forwarder pattern doesn't break `SmackInstGenerator`
   visitGEP / visitLoad / visitStore inlining. ~800 LOC out.

3. **Carve out `SmackExprRep`.** Mostly free-functioning, but
   `expr(Value*)` is called by everyone so the forwarder must be
   inline + perf-neutral. ~500 LOC out.

4. **Carve out `SmackContractRep`.** Smallest, well-bounded. Includes
   the Phase 3.5 `fatalUserError` helper, which moves into
   `SmackContractRep.cpp` as `namespace { ... }`. ~342 LOC out.

5. **Repeat for `Prelude.cpp` (1864 LOC).** The Gen sub-classes are
   already structurally split inside the file; just promote each
   `*Gen` block to its own `.cpp` + `.h`. Header
   `include/smack/Prelude.h` already declares all the Gen classes —
   the split is essentially moving definitions across files without
   touching declarations. Estimated 4 new `.cpp` files
   (`TypeDeclGen.cpp`, `ConstDeclGen.cpp`, `MemDeclGen.cpp`,
   `IntOpGen.cpp`, `PtrOpGen.cpp`, `FpOpGen.cpp`) of ~300 LOC each.

6. **Repeat for `SmackInstGenerator.cpp` (1699 LOC).** Natural split is
   per visit-method category:
   - `SmackInstMemOps.cpp` (visitLoad, visitStore, visitGEP, visitAlloca)
   - `SmackInstArith.cpp` (visitBinaryOperator, visitCast, visitICmp,
     visitFCmp)
   - `SmackInstControl.cpp` (visitBranch, visitSwitch, visitPHI,
     visitReturn, visitCall)
   - `SmackInstSpecial.cpp` (visitIntrinsic, visitAtomicRMW,
     visitVectorOp, visitInsertValue/ExtractValue)
   The visitor pattern stays in `SmackInstGenerator.h`; the per-instruction
   methods become free functions called from inside the visitor.

## CMake wiring

For each PR add the new `.cpp` files to the `smackTranslator` library
list in `CMakeLists.txt` (around lines 163-194). No new library targets
needed; everything stays in `smackTranslator` so consumers don't break.

## Risk + verification

Per-PR:

1. Build `smack_unittests` + run `ctest --test-dir build-tests` — should
   stay at the post-Phase-3.5 baseline (109+ cases).
2. Run the regtest matrix on `c/basic` + `c/contracts` (annotation paths
   exercise the Phase 3.5 `valueAnnotation` code most heavily).
3. Diff the generated `.bpl` for a representative regtest fixture
   before/after — must be byte-identical. `tools/llvm_feature_audit.py`
   already does feature diffs; extend to a Boogie-output diff for the
   facade pass.
4. Run `cmake --build build-fuzz --target fuzz_boogie_ast_print` (Phase
   5.2 fuzz target) for 2 min as part of the PR — any printer regression
   surfaces fast.

## What this is NOT

- Not a behavior change. Every method's contract preserved.
- Not a header-split that breaks downstream `find_package(smack)` users.
  Public `SmackRep.h` stays. Sub-class headers ship under
  `include/smack/internal/` (not in the installed surface).
- Not a `legacy::PassManager` removal — that's Phase 2.

## Coordination

Each PR rebases on the same baseline (post-Phase-3.5 main). Bundling all
six PRs sequentially is fine; doing them in parallel guarantees nasty
merge conflicts in `SmackRep.cpp`. Single author, six commits, one
release.

## When to start

After Phase 2.3 (sea-dsa NewPM port) lands and `lib/smack/` settles. The
sea-dsa bridge in `DSAWrapperAnalysis.cpp` doesn't touch `SmackRep`, so
the orderings are independent, but the C++ build queue gets long when
both phases land in flight.

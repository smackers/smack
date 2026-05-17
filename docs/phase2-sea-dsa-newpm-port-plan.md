# Phase 2 — NewPM default + sea-dsa NewPM port

## Why this is blocked

`include/smack/DSAWrapperAnalysis.h` already exposes sea-dsa as a NewPM
`ModuleAnalysis` — but the implementation in
`lib/smack/DSAWrapperAnalysis.cpp` does it by holding a
`std::unique_ptr<llvm::legacy::PassManager>` for the lifetime of the
analysis result. That works (and is even semantically clean — the
`PassManager` owns the legacy `DSAWrapper` pass, the NewPM result holds
a non-owning observer), but it means:

- The legacy `PassManager` and all its registration glue stay in the
  build forever. `lib/smack/SmackPipeline.cpp`'s `runSmackTier*` legacy
  composer cannot be deleted.
- Every NewPM consumer of `DSAWrapperAnalysis` pays the cost of
  rebuilding sea-dsa's analysis on every cache miss because the bridge
  doesn't participate in NewPM's preservation tracking.
- `SMACK_NEW_PM` stays opt-in (`OFF` default at `CMakeLists.txt:325`)
  because the legacy bridge masks real latency regressions the corpus
  audit would otherwise catch.

The Phase 2 endgame is to replace sea-dsa's legacy passes with NewPM
analyses end-to-end, then drop the bridge.

## Scope of the upstream port

Files in sea-dsa that need NewPM siblings:

| sea-dsa upstream file               | What it is                                | NewPM target                              |
|-------------------------------------|--------------------------------------------|--------------------------------------------|
| `seadsa/AllocWrapInfo.hh/.cc`       | `llvm::ImmutablePass`                      | `AllocWrapInfoAnalysis : AnalysisInfoMixin` |
| `seadsa/DsaLibFuncInfo.hh/.cc`      | `llvm::ImmutablePass`                      | `DsaLibFuncInfoAnalysis : AnalysisInfoMixin`|
| `seadsa/DsaAnalysis.hh/.cc`         | `llvm::ModulePass`                         | `DsaAnalysisAnalysis : AnalysisInfoMixin`   |
| `seadsa/CompleteCallGraph.hh/.cc`   | `llvm::ModulePass`                         | `CompleteCallGraphAnalysis : AnalysisInfoMixin` |
| `seadsa/support/RemovePtrToInt.hh`  | `llvm::FunctionPass`                       | `RemovePtrToIntPass : PassInfoMixin`        |

The first four are analyses (no IR mutation). They can be ported by:

1. Replacing the `llvm::Pass` / `llvm::ImmutablePass` /
   `llvm::ModulePass` base with `AnalysisInfoMixin<T>`.
2. Adding a `static AnalysisKey Key;` member + the
   `friend AnalysisInfoMixin<T>;` declaration.
3. Renaming `runOnModule` / `getAnalysisUsage` / `doInitialization` into
   a single `Result run(Module &M, ModuleAnalysisManager &MAM);`.
4. Replacing all `getAnalysis<Other>()` lookups inside `run` with
   `MAM.getResult<OtherAnalysis>(M)`.

`RemovePtrToInt` is a transform; the NewPM equivalent is
`PassInfoMixin<RemovePtrToIntPass>` with a `PreservedAnalyses
run(Function &, FunctionAnalysisManager &)`.

## Strategy

The aggressive option is to fork. The conservative option is to
upstream + bump. Aggressive scope per the modernization plan picks
**fork** with intent to upstream:

1. Add a vendored second submodule `external/sea-dsa-newpm/` pointing
   at the swoosh-org fork (to be created).
2. The fork commits a NewPM port branch on top of upstream HEAD. PRs
   open against the seahorn org as the port stabilizes; once accepted
   upstream, the vendored fork retires.
3. Inside SMACK, keep the legacy submodule `sea-dsa/` building too
   during the transition. `option(SMACK_USE_LEGACY_SEADSA "..." OFF)`
   in `CMakeLists.txt` selects which.

## Mechanical migration order

Each numbered step is a single PR. Each keeps `SMACK_NEW_PM=OFF` the
default — flipping it is the very last step.

1. **Fork sea-dsa.** Create `swoosh/sea-dsa-newpm` on github. Submodule
   it under `external/sea-dsa-newpm/`. CI gates the build (no port
   yet — just a vendored copy of upstream HEAD with submodule pin
   added to `tools/submodule-pins.txt`).

2. **Port `AllocWrapInfo` + `DsaLibFuncInfo`** (the immutable passes
   first — simplest). Add NewPM siblings; keep legacy classes as
   thin wrappers that delegate so existing SMACK consumers still
   compile.

3. **Port `DsaAnalysis`.** This is the big one. Touch points: the new
   `DsaAnalysisAnalysis::run` allocates the `DsaAnalysis` state +
   walks all functions. Validate by comparing the `Graph` output
   pre/post-port for every regtest fixture in `c/basic` + `c/data`.

4. **Port `CompleteCallGraph`.** Smaller than `DsaAnalysis`. Same
   pattern.

5. **Port `RemovePtrToInt`** as a NewPM `PassInfoMixin`. Replace
   `seadsa::createRemovePtrToIntPass()` callers in
   `lib/smack/SmackPipeline.cpp` with a `FunctionPassManager::addPass`.

6. **Update SMACK's `DSAWrapperAnalysis`** to consume the new
   `DsaAnalysisAnalysis` directly:

   ```cpp
   DSAWrapperAnalysis::Result
   DSAWrapperAnalysis::run(llvm::Module &M,
                           llvm::ModuleAnalysisManager &MAM) {
     auto &dsa = MAM.getResult<seadsa::DsaAnalysisAnalysis>(M);
     // Build the SMACK-level wrapper around the live sea-dsa state.
     auto wrapper = std::make_unique<DSAWrapper>(dsa, …);
     Result r;
     r.wrapper = std::move(wrapper);
     return r;
   }
   ```

   The `legacy::PassManager` member is **deleted**. Same change for
   `CompleteCallGraphAnalysis`.

7. **Delete the legacy-PM bridge.** No more
   `legacy::PassManager` / `legacy::FunctionPass` includes anywhere
   under `lib/smack/`. Add a clang-tidy rule banning them so future
   PRs can't regress.

8. **Delete legacy SmackPipeline.** Remove the `#ifndef SMACK_NEW_PM`
   branches in `tools/llvm2bpl/llvm2bpl.cpp` + `runSmackTierANewPM` /
   `runSmackFullNewPM` become the only entry points. Remove the
   `SMACK_NEW_PM` option from `CMakeLists.txt`.

9. **Run the corpus equivalence audit.** Extend
   `tools/llvm_feature_audit.py` with a `--boogie-diff` mode that runs
   the old + new pipelines on every regtest C input + diffs the
   resulting `.bpl` file with a normalized canonicalizer (sort `assume`
   attributes, normalize Boogie variable suffixes). The audit must
   show zero divergence before step 10.

10. **Flip the default.** `option(SMACK_NEW_PM "..." ON)`. CI matrix
    keeps an opt-out `SMACK_USE_LEGACY_PM=ON` knob for one release as
    an escape hatch, then drops.

## Risk + verification

- Each step rebases on post-Phase-3.x main and runs the full regtest
  matrix (the GitHub Actions `check-regressions` job covers 28 folders).
  Pass count must match the README baseline (978/979) before merge.
- Sanitizer CI (`cpp-sanitizers` job) catches use-after-free regressions
  if the new analysis result lifetime semantics drift.
- Reproducible build CI catches non-determinism that the legacy PM's
  initialization order quietly hid.
- `fuzz_bitcode_parse` + `fuzz_boogie_ast_print` extend the
  defense-in-depth without needing per-step changes.

## What this is NOT

- Not a rewrite of sea-dsa's analysis logic. The actual `Graph`
  construction is unchanged. Only the pass-registration plumbing
  swaps.
- Not removal of `boost::hash_combine` or other sea-dsa C++17-deprecation
  cleanups. Those are upstream's call.
- Not a fix for the `-Wdeprecated-declarations` warnings the SMACK
  build silences at `CMakeLists.txt:248-251`. That's a separate
  hygiene PR after step 6.

## Coordination with Phase 3.2

The two phases are independent (Phase 3.2 splits `SmackRep`; Phase 2
swaps `DSAWrapperAnalysis`'s implementation). Doing both in flight at
the same time guarantees merge conflicts in `SmackRep.cpp`'s
`oracleModifiesForFunction` (which reaches into `Regions`, which
reaches into `DSAWrapperAnalysis`). Pick one to land first; the other
rebases.

Recommended ordering: Phase 2 first. It's the bigger architectural
change and the harder one to test; getting it green frees the
SmackRep split to land without sea-dsa flux underneath.

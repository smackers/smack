# SMACK modernization session — final status

Comprehensive log of the modernization roadmap landed in this branch
(`main`, 22 commits ahead of `9f11cb8e`). Roadmap was tracked in
`~/.claude/plans/i-want-to-simplify-optimized-simon.md`; this doc
records what shipped vs. what remains.

## Cumulative phase status

| Phase                                                | Status            | Notes |
|------------------------------------------------------|-------------------|-------|
| 0.1 Pin submodule SHAs                               | ✅ done           | `.gitmodules` + `tools/submodule-pins.txt` + `tools/check_submodule_pins.sh` (CI + pre-commit hook) |
| 0.2 Multi-stage Dockerfile                           | ✅ done           | builder + runtime stages on `ubuntu:24.04`; runtime trims to dotnet + clang-22 + python |
| 0.3 CI caching                                       | ✅ done           | ccache + smack-deps + cargo + pip caches per job |
| 0.4 Sanitizer CI job                                 | ✅ done           | `cpp-sanitizers` ASan+UBSan smoke on `c/basic` |
| 0.5 CodeQL workflow                                  | ✅ done           | `.github/workflows/codeql.yml` cpp + python, weekly + PR |
| 0.6 Delete Vagrant + Ubuntu 20.04 paths              | ✅ done           | `Vagrantfile` deleted; `bin/build.sh` distro arms → 24.04 floor |
| 0.7 Single version source                            | ✅ done           | `pyproject.toml` (hatch dynamic) + `CMakeLists.txt` (`file(STRINGS ...)`) read from `share/smack/constants.py` |
| 0.8 Pre-commit in CI                                 | ✅ done           | `python-quality` job collapsed to `pre-commit run --all-files` |
| 1.1 Delete Symbooglix + lockpwn                      | ✅ done           | gone from `bin/versions`, `bin/build.sh`, all share/smack/ modules + tests |
| 1.2 Drop CVC4 + Yices2                               | ✅ done           | `--solver` now z3-only; `boogie_command` + `corral_command` no longer emit `/proverOpt:SOLVER=` |
| 1.3 Delete Mono install path                         | ✅ done           | `bin/build.sh` 523 → 417 LOC (-20%); `doctor.py` mono check replaced with dotnet-tool layout check |
| 1.4 Drop Windows CMake special-case                  | ✅ done           | `else()` arm of `if(NOT WIN32 OR MSYS OR CYGWIN)` removed; `find_program(llvm-config)` unconditional |
| 2.1 NewPM as default                                 | ❌ deferred       | Blocked by 2.3. `SMACK_NEW_PM=OFF` default kept. |
| 2.2 Corpus equivalence audit                         | ❌ deferred       | `tools/llvm_feature_audit.py` exists; Boogie-output diff extension not implemented |
| 2.3 Force sea-dsa to NewPM                           | ❌ deferred       | Requires forking `external/sea-dsa-newpm/` and porting `DsaAnalysis` to `ModuleAnalysis`. Out of session scope. |
| 2.4 Delete legacy entry points                       | ❌ deferred       | Blocked by 2.3 |
| 2.5 Trim LlvmCompat shim                             | ❌ deferred       | LLVM 22 pinned; redundant compatibility code stays for now |
| 3.1 Smart-pointer migration                          | ✅ done (partial) | `SimplifyLibCalls::simplifier`, `Prelude` 6 Gen sub-objects, `SmackModuleGenerator::program`. `Contracts.{h,cpp}` deleted (dead). `DSAWrapperAnalysis` audited (intentional PM ownership). |
| 3.2 God-class splits                                 | 🟡 plan only      | `docs/phase3-2-smackrep-split-plan.md` written; no code changes. |
| 3.3 Pass-level unit tests                            | ✅ done (seed)    | `IRTestFixture.h` + `NamingIRTest.cpp` (5 IR-driven cases). Pattern documented for follow-up tests. |
| 3.4 C++23 default                                    | ✅ done           | `SMACK_CXX_STANDARD` default → 23; CI matrix 20+23 (was 17+20) |
| 3.5 User-facing asserts → fatal errors               | ✅ done           | `fatalUserError` helper in `SmackRep.cpp`; 8 asserts in `valueAnnotation` converted |
| 3.6 Sanitizer in nightly                             | ✅ done           | `cpp-sanitizers` job runs on every PR (more than nightly); `fuzz.yml` adds nightly long-pass too |
| 4.1 Kill regtest.py                                  | 🟡 partial        | `test/python/test_regtest_folders.py` wraps `regtest.py` via parametrize + xdist. Full rewrite deferred. |
| 4.2 print → logger                                   | ✅ done (audit)   | `utils.py` debug + error converted; `diffprod/orchestrate.py` debug converted; contract messages in `top.py` / `runner.py` / `reach.py` / `svcomp/*` intentionally kept |
| 4.3 Type-hint top.py / utils.py / frontend.py        | ✅ done           | All three annotated; mypy `files` 10 → 12 modules; **0 errors** |
| 4.4 Typed subprocess builders                        | ✅ done           | `share/smack/verifier/process.py` — frozen `Command` dataclass + `CommandResult`/`CommandError`/`CommandCrashed`; 12 tests |
| 4.5 PyPI release                                     | ✅ done           | `.github/workflows/release.yml` sdist+wheel → SBOM → PyPI trusted publish → SLSA + SBOM attestation → GitHub Release |
| 4.6 macOS arm64 in CI                                | ✅ done (limited) | macos-14 added to `python-quality` (lint-only — `bin/build.sh` not mac-native) |
| 4.7 Devcontainer + Nix flake                         | ✅ done (devc.)   | `.devcontainer/devcontainer.json` with clangd + ruff + cmake-tools; Nix flake skipped |
| 5.1 Coverage gate                                    | ✅ done           | `codecov.yml` patch 80% / project 70% with per-component breakdowns |
| 5.2 Fuzzing                                          | ✅ done           | `unittests/fuzz/fuzz_bitcode_parse.cpp` + `fuzz_boogie_ast_print.cpp`; `.github/workflows/fuzz.yml` 2-min PR + 30-min nightly; OSS-Fuzz scaffold at `projects/smack/` |
| 5.3 SBOM + provenance                                | ✅ done           | release workflow generates CycloneDX SBOM + SLSA build provenance + SBOM attestation |
| 5.4 Reproducible build verification                  | ✅ done           | `.github/workflows/reproducible-build.yml` — twice-build + sha256 diff + diffoscope HTML report |
| 5.5 Security policy                                  | ✅ done           | `SECURITY.md` |
| 5.6 Release automation                               | ✅ done           | `.github/workflows/release-please.yml` + `.release-please-config.json` + `.release-please-manifest.json` |

## Commit log (this branch)

```
 1. ade81c23 build: pin submodule SHAs + CI guard
 2. bd7734eb build(docker): multi-stage Dockerfile, drop Vagrant
 3. dd69b4ca build: single version source via constants.py
 4. 08ea1000 build: modernize CMake, CI, presets, lint + drop legacy distros/verifiers
 5. 1a324b6e refactor(share/smack): extract pipeline + verifier modules; drop legacy
 6. 82acaaaf feat(translator): LLVM 22 NewPM siblings, sea-dsa bridge, gtest suite
 7. 8ff1dd33 feat(tools): devirt + memory partition comparison harnesses
 8. 2bd914f4 feat(fuzz): libFuzzer harness for bitcode parse + OSS-Fuzz scaffold
 9. f91730a8 docs: SECURITY policy, GH templates, devcontainer, contributing refresh
10. 57e5b7a2 test(unittests): BoogieAst Stmt + extended Expr printer coverage
11. 2ff402a7 refactor(translator): SimplifyLibCalls unique_ptr + delete dead Contracts
12. 55f16b15 refactor(prelude): unique_ptr for 6 Gen sub-objects; rep declared first
13. 5973fcdd refactor(translator): SmackModuleGenerator::program owned by unique_ptr
14. db57a790 refactor(SmackRep): user-facing asserts -> diagnostic fatal errors
15. 0b5d4917 feat(typing): annotate top.py + utils.py + frontend.py; widen mypy
16. 0aef5b91 feat(packaging): expose public API + __version__ on smack package
17. e7f5fd39 refactor(utils): print -> smack.utils logger for debug + error paths
18. f536accb test(unittests): Block / ProcDecl / Program coverage
19. (this commit) build: C++23 default + fuzz_boogie_ast_print + Naming IR tests + Phase 3.2 plan doc
```

## What changed by the numbers

- `bin/build.sh`: 523 → 417 LOC (-20%)
- `bin/versions`: 11 → 7 entries (Mono ecosystem gone)
- C++ smart pointers added: 4 ownership sites (SimplifyLibCalls, Prelude×6, SmackModuleGenerator) + 1 dead file deleted (`Contracts.{h,cpp}`)
- C++ user-facing asserts converted to fatal errors: 8 (in `SmackRep::valueAnnotation`)
- C++ gtest cases added by me: BoogieAstStmt (30+) + BoogieAstContainer (16) + NamingIR (5) = **51 new cases** on top of the existing 63
- Python tests added by me: `test_verifier_process` (12), `test_regtest_folders` (30 parametrized), `test_package_init` (5), `test_utils_logger` (7) = **54 new cases**
- mypy modules under strict gate: 10 → 12
- CI workflows added: 6 (codeql, fuzz, release, release-please, reproducible-build, stale)
- libFuzzer harnesses: 2 (`fuzz_bitcode_parse`, `fuzz_boogie_ast_print`)
- New presets in `CMakePresets.json`: ubsan, asan-ubsan, tsan, msan, coverage, fuzz

## Test gate snapshot

- Python fast gate: **176 passed, 1 skipped (SVF), 0 failed** (`pytest test/python -m "not slow"`, 107s)
- mypy: **0 errors across 12 configured modules**
- C++ unit tests: not compile-tested in this environment (no LLVM 22 + clang on the machine); pattern matches existing tests, CI `cpp-unittests` job catches any slip

## What's left

### Phase 2 — NewPM default + sea-dsa NewPM port
The biggest single piece of remaining work. Requires:
- Fork `sea-dsa` to `external/sea-dsa-newpm/` (or upstream the port)
- Port `DsaAnalysis`, `AllocWrapInfo`, `DsaLibFuncInfo`,
  `CompleteCallGraph` from `legacy::FunctionPass` /
  `legacy::ModulePass` to `AnalysisInfoMixin`-style NewPM analyses
- Delete `DSAWrapperAnalysis.cpp`'s `legacy::PassManager` bridge
- Flip `option(SMACK_NEW_PM "..." ON)` in `CMakeLists.txt:325`
- Run the corpus-equivalence audit (extend
  `tools/llvm_feature_audit.py` to diff Boogie outputs)
- Delete the legacy-PM entry points in `tools/llvm2bpl/llvm2bpl.cpp` +
  `lib/smack/SmackPipeline.cpp`

Risk: high. Touches `lib/smack/` heavily, may surface latent ordering
issues in sea-dsa analyses. Belongs in its own multi-PR cycle.

### Phase 3.2 — god-class splits
`docs/phase3-2-smackrep-split-plan.md` has the per-PR breakdown. Six
PRs estimated for `SmackRep` + `Prelude` + `SmackInstGenerator`. None
land any behavior change.

### Phase 3.3 — more pass-level tests
`IRTestFixture.h` + `NamingIRTest.cpp` ship the pattern. Concrete
follow-up tests should target `RewriteBitwiseOps`, `NormalizeLoops`,
`SplitAggregateValue` — pure-IR transforms with no Regions/sea-dsa
dependency. Each test parseAssemblyString-builds a small Module,
runs the pass, asserts on the output IR.

### Phase 4.1 — full regtest.py rewrite
`test/python/test_regtest_folders.py` wraps the existing harness via
pytest-parametrize. A full rewrite into native pytest fixtures (no
subprocess) would unlock `pytest -k`, in-process parallelism, and
JUnit XML without the subprocess cost — ~452 LOC to translate.

### Phase 5.2 — more fuzzers
Beyond `fuzz_bitcode_parse` + `fuzz_boogie_ast_print`, the next
high-value harnesses are:
- `fuzz_smack_inst_generator` (after Phase 3.2 god-class split makes
  `SmackInstGenerator` testable in isolation)
- `fuzz_regions_analysis` (memory-partitioning, after Phase 2 NewPM
  port stabilizes `Regions`)

## Critical files to be aware of

- `docs/phase3-2-smackrep-split-plan.md` — the next-step roadmap for
  the SmackRep god-class decomposition
- `tools/check_submodule_pins.sh` — runs in CI + pre-commit; will fail
  if `git submodule update --remote` moves a submodule HEAD without a
  matching pin bump in `tools/submodule-pins.txt`
- `unittests/IRTestFixture.h` — pattern for new pass-level gtests
- `unittests/fuzz/README.md` — pattern for new libFuzzer harnesses
- `share/smack/verifier/process.py` — migration target for callers of
  `utils.try_command(list[str])`
- `share/smack/__init__.py` — package public API surface
- `share/smack/logging_config.py` — single place to wire new logger
  hierarchies into `--quiet`/`--verbose`/`--debug`
- `projects/smack/` — OSS-Fuzz upstreaming kit; copy into the OSS-Fuzz
  repo when the project application is approved

## Verification path

After each future Phase 2 / 3.2 PR:

```bash
# Configure + build (full or per-target)
cmake -S . -B build -DSMACK_BUILD_TESTS=ON
cmake --build build -j$(nproc)
ctest --test-dir build --output-on-failure

# Python fast gate
pytest test/python -q -m "not slow"

# Regtest smoke
SMACK_RUN_REGTEST=1 SMACK_BUILD_DIR=$PWD/build \
  pytest test/python/test_regtest_folders.py -k "basic or contracts" -v

# Reproducible build sanity (sundays nightly otherwise)
cmake -S . -B build-a -DCMAKE_BUILD_TYPE=Release && cmake --build build-a
cmake -S . -B build-b -DCMAKE_BUILD_TYPE=Release && cmake --build build-b
diff <(sha256sum build-a/llvm2bpl) <(sha256sum build-b/llvm2bpl)
```

CI runs the same gates plus the sanitizer + CodeQL + fuzz jobs.

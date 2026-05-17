# LLVM Modernization Opportunities

This document tracks the next SMACK modernization slice after the LLVM 22 port
and the opt-in NewPM pipeline. The goal is to find useful LLVM features and
efficiency work with evidence first, then make isolated implementation changes.

The matching probe is `tools/llvm_feature_audit.py`. It runs a small fixture set
through legacy `llvm2bpl`, optionally through the NewPM build, captures
`--smack-pipeline-report` JSON, records `opt-22 --print-passes`, and writes
`audit.json` plus `audit.md`. Timings are report-only diagnostics, not budgets.

Memory partitioning now has a separate probe:
`tools/memory_partition_compare.py`. It runs the same linked-bitcode style used
by the Python integration tests, emits `--smack-memory-partition-report` JSON for
each candidate, and ranks candidates by a map-count-first rule: fewer failed
fixtures, more emitted `$M.*` Boogie maps, more regions, more typed regions,
fewer fallback/imprecise regions, fewer merges, then lower wall time.

## Current Baseline

- SMACK is pinned to LLVM 22 in `bin/versions`; the local toolchain may report a
  nearby LLVM 22 patch release through `llvm-config-22 --version`.
- The legacy pipeline remains the production `llvm2bpl` path.
- `-DSMACK_NEW_PM=ON` enables the full NewPM path for equivalence and audit work.
- sea-dsa is still legacy-PM code and is bridged into NewPM through
  `DSAWrapperAnalysis` / `CompleteCallGraphAnalysis`.
- CI already runs ruff, C++ gtests, Python tests, and the regression matrix; the
  audit adds artifacts only and must not fail because one runner is slower.

## Ranked Opportunities

| ID | Area | Why It Matters | First Action |
| --- | --- | --- | --- |
| `bpl-output-streaming` | Efficiency | Early reports show Boogie emission dominates translator time on small and medium fixtures, and both BPL printers stage output in `std::ostringstream` before writing it. | Prototype direct streaming from `Program::print` to the destination stream, then require byte-for-byte BPL equality and timing comparison. |
| `newpm-analysis-preservation` | NewPM | Many SMACK NewPM siblings conservatively return `PreservedAnalyses::none()` after mutation. More precise preservation may reduce repeated analysis work once NewPM is the default candidate. | Audit each pass for DominatorTree, LoopInfo, and module-analysis preservation before changing pass order. |
| `llvm-standard-instrumentations` | Observability | LLVM already provides NewPM instrumentation helpers; SMACK now has custom report callbacks and should compare them against upstream facilities. | Prototype `StandardInstrumentations` / time profiling behind the existing report flag and keep the current JSON schema stable unless the replacement is clearly better. |
| `llvm22-ptrtoaddr` | LLVM IR | LLVM 22 introduced `ptrtoaddr`, which separates address extraction from pointer provenance capture. SMACK still has explicit ptr-to-int cleanup and sea-dsa-based pointer reasoning. | Add focused IR fixtures for `ptrtoaddr`; do not alter pointer lowering until those fixtures preserve expected BPL behavior. |
| `llvm-attributor-candidates` | LLVM features | LLVM 22 exposes inference passes such as Attributor that may simplify IR before translation, but verifier semantics can be fragile. | Run candidate passes only in exploratory builds and diff emitted BPL before considering production use. |
| `memory-partitioning-evidence` | Memory model | SMACK now defaults to SeaDsa bottom-up splitting because it emits more disjoint maps on the BearSSL fixture. The comparison suite also names TeaDsa-style SeaDsa and the opt-in LLVM-AA overlay so they can be ranked against the default. | Run `tools/memory_partition_compare.py`, inspect `partition-comparison.md`, then keep only refinements that improve map count without verifier regressions. |

## Report-Only Workflow

```sh
python3 tools/llvm_feature_audit.py \
  --legacy-llvm2bpl build-llvm22c/llvm2bpl \
  --newpm-llvm2bpl build-newpm/llvm2bpl \
  --out-dir build/llvm-audit
```

Expected outputs:

- `audit.json`: machine-readable LLVM/tool paths, fixture reports, pass inventory,
  and opportunity records.
- `audit.md`: compact human summary for CI artifacts.
- `*.legacy.json` and `*.newpm.json`: raw per-fixture pipeline reports.
- `*.legacy.bpl` and `*.newpm.bpl`: generated BPL for follow-up diffing.

## Memory Partitioning Workflow

```sh
python3 tools/memory_partition_compare.py \
  --llvm2bpl build-llvm22c/llvm2bpl \
  --out-dir build/memory-partition-compare
```

Default candidates:

- `sea-dsa-ci`, `sea-dsa-bu`, `sea-dsa-butd-cs`, `sea-dsa-cs`, `sea-dsa-flat`
- `teadsa-butd-cs-type-aware`
- `cell-refined-ci`, `cell-refined-butd-cs`
- `aa-refined-bu`, `aa-refined-teadsa`

Expected outputs:

- `partition-comparison.json`: machine-readable candidate runs, raw report paths,
  and ranking data.
- `partition-comparison.md`: compact table for CI artifacts and review.
- optional external candidate probes when `--probe-external-candidates` or
  `--external-candidate NAME=TOOL[,TOOL]` is used. SVF `wpa` can now run as a
  sidecar MemorySSA comparison (`distinct`, `intra-disjoint`, and
  `inter-disjoint`); those rows are intentionally kept out of the main SMACK
  `$M.*` ranking until an adapter can emit sound SMACK memory maps.
- `*.memory.json`: raw memory partition reports from `llvm2bpl`.
- `*.bpl`: generated Boogie files for behavioral diffing.

Current implementation notes:

- The production default remains `sea-dsa`, now with `-sea-dsa=bu`.
- `--sea-dsa-mode` exposes SeaDsa `ci`, `bu`, `butd-cs`, `cs`, and `flat` through
  the Python driver so context-sensitive modes can be tested without patching.
- `--memory-partitioner=cell-refined` is experimental and opt-in. It keeps the
  old merge behavior except that complicated regions with different concrete
  representatives are no longer forced together only because both are
  complicated.
- `--memory-partitioner=aa-refined` is experimental and opt-in. It starts from
  SeaDsa-derived regions and only avoids a merge when LLVM AA proves `NoAlias`
  for a valid same-function query.
- LLVM `MemorySSA` is useful for future sparse memory-use evidence, but it is
  intraprocedural and should be treated as a complement to pointer partitioning,
  not a drop-in replacement for SeaDsa-derived regions.
- Future partitioning candidates worth prototyping are an SVF-backed points-to
  importer, TeaDsa-style anti-oversharing refinements, LLVM AA/noalias/TBAA
  evidence layered on top of BU, and segmented-memory-style grouping for large
  symbolic pointer target sets.

## References

- [LLVM 22 release notes](https://releases.llvm.org/22.1.0/docs/ReleaseNotes.html)
- [LLVM New Pass Manager](https://releases.llvm.org/22.1.0/docs/NewPassManager.html)
- [`opt` command guide](https://releases.llvm.org/22.1.0/docs/CommandGuide/opt.html)
- [LLVM `StandardInstrumentations`](https://llvm.org/doxygen/classllvm_1_1StandardInstrumentations.html)
- [LLVM optimization remarks](https://llvm.org/docs/Remarks.html)
- [LLVM MemorySSA](https://www.llvm.org/docs/MemorySSA.html)
- [LLVM Alias Analysis Infrastructure](https://llvm.org/docs/AliasAnalysis.html)
- [SMACK: Decoupling Source Language Details from Verifier Implementations](https://soarlab.org/papers/2014_cav_re.pdf)
- [Data Structure Analysis: An Efficient Context-Sensitive Heap Analysis](https://llvm.org/pubs/2003-04-29-DataStructureAnalysisTR.html)
- [Unification-based Pointer Analysis without Oversharing](https://arxiv.org/abs/1906.01706)
- [SVF: Static Value-Flow Analysis Framework](https://svf-tools.github.io/SVF/)
- [cclyzer++](https://galoisinc.github.io/cclyzerpp/)
- [PhASAR](https://github.com/secure-software-engineering/phasar)
- [Phoenix: A Modular and Versatile Framework for C/C++ Pointer Analysis](https://arxiv.org/abs/2602.01720)
- [A Segmented Memory Model for Symbolic Execution](https://srg.doc.ic.ac.uk/files/papers/segmem-esecfse-19.pdf)
- [Byte-Precise Verification of Low-Level List Manipulation](https://www.fit.vut.cz/person/vojnar/public/Publications/dpv-sas-13.pdf)

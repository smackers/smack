[![main branch ci status](https://github.com/smackers/smack/workflows/SMACK%20CI/badge.svg?branch=main)](https://github.com/smackers/smack/actions)
[![develop branch ci status](https://github.com/smackers/smack/workflows/SMACK%20CI/badge.svg?branch=develop)](https://github.com/smackers/smack/actions)

> Fork notice: this repository is Alex Thomas's Swoosh-oriented fork of
> [SMACK](https://github.com/smackers/smack). The upstream SMACK project,
> license, acknowledgements, and documentation are preserved below.

## Fork Modernization Status (2026-05)

This fork ports SMACK to LLVM 22 and adds modernization across both the C++ pass
pipeline and the Python tooling. Highlights:

**C++ / LLVM**
- LLVM 22 compatibility via `include/smack/LlvmCompat.h` shim
- 22 NewPM siblings of legacy passes (Tier A leaves through Tier D sinks)
- `runSmackFullNewPM` composes the full NewPM pipeline; sea-dsa (still legacy
  upstream) is wrapped via `DSAWrapperAnalysis` / `CompleteCallGraphAnalysis`
  legacy-PM-as-MAM-analysis bridges
- Build with `-DSMACK_NEW_PM=ON` to route `llvm2bpl` through NewPM (default off;
  legacy remains the production path while corpus equivalence stays under CI)
- Default C++20 build, with C++17 compatibility kept under CI via
  `-DSMACK_CXX_STANDARD=17`
- CMakePresets.json (`debug`/`release`/`relwithdebinfo`/`asan`)
- Target-scoped `include_directories` (no more globals)
- `cmake/smack-config.cmake.in` enables downstream `find_package(smack)`
- gtest harness via FetchContent (`SMACK_BUILD_TESTS=ON`); 63 unit tests

**Python (`share/smack/`)**
- `top.py` decomposed from 1832 → 122 lines (-93%) into 10 sub-modules:
  - `cli/results.py` (VResult/VProperty)
  - `cli/parser.py` (argparse)
  - `verifier/{commands,runner,portfolio}.py`
  - `pipeline/{transform,translate,frontend}.py`
  - `diffprod/orchestrate.py`
  - `constants.py` (VERSION + inlined_procedures)
- Original `from smack.top import X` callers preserved via re-exports
- `pyproject.toml` with hatchling backend, pinned deps, dev extras
- `ruff` configured for lint + format (`E,W,F,I,UP,B,SIM,PTH,LOG,RUF`)
- `mypy` clean across 10 sub-modules (`python_version = "3.10"`)
- Pre-commit hooks: `ruff`, `ruff-format`, `check-yaml`, `end-of-file-fixer`
- `external/deltarel` is a required submodule for relational product tests and
  runtime product construction; `SMACK_DELTAREL_ROOT` can override the checkout

**CI (`.github/workflows/smack-ci.yaml`)**
- `python-quality` job: ruff check + format-check
- `cpp-unittests` job: C++17 and C++20 gtest runs via ctest
- `python-unittests` job: extracted-module coverage, required product
  integration, and Codecov upload
- `check-regressions` 28-folder matrix gated by all three

**Testing**
- 63/63 C++ gtests pass (BoogieAst, Naming, NewPM equivalence, NewPM edge
  cases, NewPM Tier C/D, full-pipeline equivalence)
- Python fast gates cover extracted modules, pure BPL diff-product semantics,
  and required SMACK/deltarel CLI integration; larger generated-BPL product
  stress tests are marked `slow`
- End-to-end SMACK regtest matrix: **978 PASS / 1 FAIL (pre-existing) / 0
  TIMEOUT** across C+Rust+LLVM IR (with Corral: 1356+ PASS)

**Architecture references**
- `runSmackTierANewPM` / `runSmackFullNewPM` — NewPM pipeline composers in
  `lib/smack/SmackPipeline.cpp`
- `DSAWrapperAnalysis::run` — Option 2 sea-dsa-wrap pattern in
  `lib/smack/DSAWrapperAnalysis.cpp` (NewPM analysis holds `legacy::PassManager`
  for the lifetime of the cached result)
- `smack_target_setup(target)` — DRY include + LlvmCompat helper in
  `CMakeLists.txt`

**What's not modernized**
- Logging migration (B3): `print()` → `logging.getLogger("smack")` not done
- NewPM full-pipeline remains opt-in until the real-input equivalence corpus is
  strong enough to make it the default
- Generated-BPL diff-product stress coverage is intentionally `slow`; keep it
  green before broadening the required CI gate

<img src="docs/smack-logo.png" width=400 alt="SMACK Logo" align="right">

SMACK is both a *modular software verification toolchain* and a
*self-contained software verifier*. It can be used to verify the assertions
in its input programs. In its default mode, assertions are verified up to a
given bound on loop iterations and recursion depth; it contains experimental
support for unbounded verification as well. SMACK handles complicated feature
of the C language, including dynamic memory allocation, pointer arithmetic, and
bitwise operations.

Under the hood, SMACK is a translator from the [LLVM](http://www.llvm.org)
compiler's popular intermediate representation (IR) into the
[Boogie](https://github.com/boogie-org/boogie) intermediate verification language (IVL).
Sourcing LLVM IR exploits an increasing number of compiler front-ends,
optimizations, and analyses. Currently SMACK only supports the C language via
the [Clang](http://clang.llvm.org) compiler, though we are working on providing
support for additional languages. Targeting Boogie exploits a canonical
platform which simplifies the implementation of algorithms for verification,
model checking, and abstract interpretation. Currently, SMACK leverages the
[Boogie](https://github.com/boogie-org/boogie) and [Corral](https://github.com/boogie-org/corral)
verifiers.

See below for system requirements, installation, usage, and everything else.

*We are very interested in your experience using SMACK. Please do contact
[Zvonimir](mailto:zvonimir@cs.utah.edu), [Michael](mailto:michael.emmi@gmail.com), or
[Shaobo](mailto:shaobohe@baidu.com) with any possible feedback.*


### Support

* For general questions, first consult the [FAQ](docs/faq.md).

* If something is otherwise broken or missing, open an [issue](https://github.com/smackers/smack/issues).

* As a last resort, send mail to 
  [Michael](mailto:michael.emmi@gmail.com), [Zvonimir](mailto:zvonimir@cs.utah.edu),
  and [Shaobo](mailto:shaobohe@baidu.com).

* To stay informed about updates, you can watch SMACK's Github page.


### Acknowledgements

SMACK project has been partially supported by funding from the National Science
Foundation, VMware, Amazon, and Microsoft Research. We also rely on University of
Utah's [Emulab](http://www.emulab.net/) infrastructure for extensive
benchmarking of SMACK.


### Table of Contents

1. [System Requirements and Installation](docs/installation.md)
1. [Running SMACK](docs/running.md)
1. [Demos](docs/demos.md)
1. [FAQ](docs/faq.md)
1. [Inline Boogie Code](docs/boogie-code.md)
1. [Contribution Guidelines](CONTRIBUTING.md)
1. [Projects](docs/projects.md)
1. [Publications](docs/publications.md)
1. [People](docs/people.md)

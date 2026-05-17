## Contribution Guidelines

### Local dev setup (fork modernization)

After cloning, set up the pre-commit hooks + Python dev env once:

```sh
# 0. Required submodules, including external/deltarel
git submodule update --init --recursive

# 1. Python tooling (ruff, mypy, pytest, pre-commit)
pip install -e ".[dev]"
pip install -e external/deltarel

# 2. Pre-commit hooks (auto-run ruff + format on every commit)
pre-commit install

# 3. Verify lint + format gates
ruff check share/ test/python/ tools/
ruff format --check share/ test/python/ tools/
mypy --config-file pyproject.toml

# 4. Run Python unit tests
PYTHONPATH=share pytest test/python/test_cli_smoke.py test/python/test_verifier_commands.py \
                    test/python/test_pipeline_transform.py test/python/test_pipeline_translate.py

# 5. Run required product/integration tests
PYTHONPATH=share:external/deltarel SMACK_DELTAREL_ROOT=external/deltarel \
  pytest test/python -q -m "not slow" --no-header
```

Set `SMACK_DELTAREL_ROOT=/path/to/deltarel` if you need to test a local
checkout outside `external/deltarel`.

For the C++ side:

```sh
# Default C++23 build with legacy PassManager
cmake -S . -B build && cmake --build build -j$(nproc)

# Opt into full NewPM pipeline (Tier A+B+C+D via runSmackFullNewPM)
cmake -S . -B build-newpm -DSMACK_NEW_PM=ON && cmake --build build-newpm -j$(nproc)

# C++20 compatibility mode (one-cycle escape hatch for the C++23 default)
cmake -S . -B build-cxx20 -DSMACK_CXX_STANDARD=20 && cmake --build build-cxx20 -j$(nproc)

# C++ unit tests via FetchContent + gtest
cmake -S . -B build-tests -DSMACK_BUILD_TESTS=ON
cmake --build build-tests --target smack_unittests -j$(nproc)
ctest --test-dir build-tests --output-on-failure

# Sanitizer presets (CMakePresets.json: asan / ubsan / asan-ubsan / tsan / msan / coverage / fuzz)
cmake --preset asan-ubsan
cmake --build --preset asan-ubsan --target smack_unittests
ctest --preset asan-ubsan

# libFuzzer harnesses (clang only)
cmake -S . -B build-fuzz -DSMACK_BUILD_FUZZERS=ON -DCMAKE_CXX_COMPILER=clang++
cmake --build build-fuzz --target fuzzers -j$(nproc)
build-fuzz/unittests/fuzz/fuzz_bitcode_parse unittests/fuzz/corpus/bitcode -max_total_time=60
```

### Writing new tests

| Surface                          | Pattern                                                     |
|----------------------------------|-------------------------------------------------------------|
| Pure Python helper               | `test/python/test_<module>.py`                              |
| BoogieAst printer / Stmt / Decl  | `unittests/BoogieAst*Test.cpp` — gtest, in-process          |
| LLVM-IR-driven pass + Naming     | Subclass `IRTestFixture` in `unittests/IRTestFixture.h`     |
| libFuzzer harness                | `unittests/fuzz/<name>.cpp` + `smack_add_fuzzer(...)`       |
| Boogie diff after Phase 2 work   | `python3 -m tools.boogie_normalize a.bpl b.bpl`             |
| Regtest folder (pytest wrapper)  | Mirror entry in `test/python/test_regtest_folders.py`       |
| Regtest core logic               | `test/regtest_core.py` (pure functions) — covered by pytest |

When you add a new submodule (don't), pin its SHA in
`tools/submodule-pins.txt` so the local + CI guard
(`tools/check_submodule_pins.sh`) stays green.

When you bump SMACK's version, edit only
`share/smack/constants.py` — `pyproject.toml` (hatch dynamic) and
`CMakeLists.txt` (`file(STRINGS ...)`) both read from there.




The information provided here is a must read for anyone who would like to
contribute to SMACK. Hence, please make sure to study thoroughly the following
items before you start contributing:
* We adhere to the [Contributor Covenant Code of Conduct](docs/code-of-conduct.md).
  By participating, you are expected to honor this code.
* We use this [git branching
  model](http://nvie.com/posts/a-successful-git-branching-model/). Please avoid
  working directly on the `main` branch.
* We follow guidelines for [good git commit
  practice](https://wiki.openstack.org/wiki/GitCommitMessages)
* We follow the [LLVM Coding
  Standards](http://llvm.org/docs/CodingStandards.html). We check the LLVM code
  formatting rules during continuous integration using
  [clang-format](https://clang.llvm.org/docs/ClangFormat.html).

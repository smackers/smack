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
# Default C++20 build with legacy PassManager
cmake -S . -B build && cmake --build build -j$(nproc)

# Opt into full NewPM pipeline (Tier A+B+C+D via runSmackFullNewPM)
cmake -S . -B build-newpm -DSMACK_NEW_PM=ON && cmake --build build-newpm -j$(nproc)

# C++17 compatibility mode
cmake -S . -B build-cxx17 -DSMACK_CXX_STANDARD=17 && cmake --build build-cxx17 -j$(nproc)

# C++ unit tests via FetchContent + gtest
cmake -S . -B build-tests -DSMACK_BUILD_TESTS=ON
cmake --build build-tests --target smack_unittests -j$(nproc)
ctest --test-dir build-tests --output-on-failure
```




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

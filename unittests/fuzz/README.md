# Fuzz harnesses

libFuzzer-based harnesses for the parts of the SMACK pipeline most exposed
to attacker-controlled input (bitcode parse → IR walk → Boogie codegen).

## Build

Clang is required (libFuzzer is a clang sanitizer runtime).

```bash
cmake -S . -B build-fuzz \
  -DSMACK_BUILD_FUZZERS=ON \
  -DCMAKE_C_COMPILER=clang \
  -DCMAKE_CXX_COMPILER=clang++
cmake --build build-fuzz --target fuzzers -j$(nproc)
```

## Run

Each binary takes the standard libFuzzer flags. Point at the corpus dir
and cap wall time:

```bash
build-fuzz/unittests/fuzz/fuzz_bitcode_parse \
  unittests/fuzz/corpus/bitcode \
  -max_total_time=120 \
  -print_final_stats=1
```

## Crash repro

When the fuzzer crashes it drops a `crash-<sha1>` file. Re-run the harness
with that file as the only argument to reproduce:

```bash
build-fuzz/unittests/fuzz/fuzz_bitcode_parse crash-deadbeef
```

The artifact + the ASan/UBSan stack trace are everything you need to file
an issue — keep both in the bug report.

## OSS-Fuzz

`projects/smack/` mirrors this layout for the upstream OSS-Fuzz build
once we file the project application.

## Roadmap

- `fuzz_bitcode_parse` — bitcode reader + minimal module walk. Catches
  crashes in the LLVM reader that SMACK inherits.
- `fuzz_smack_inst_generator` (TODO, after Phase 3) — drive
  `SmackInstGenerator` on synthesized small modules.
- `fuzz_boogie_ast_print` (TODO) — round-trip BoogieAst → print → parse.

Add new harnesses as `smack_add_fuzzer(name source.cpp)` in
`unittests/fuzz/CMakeLists.txt`.

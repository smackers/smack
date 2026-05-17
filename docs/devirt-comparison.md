# Devirtualization Comparison

`tools/devirt_compare.py` compares indirect-call target precision across SMACK
and external analyzers. Built-in SMACK candidates use `llvm2bpl` with
`-smack-devirt-report`; SVF and PhASAR are treated as hard comparison
dependencies when the default external candidates are enabled.

## Quick Synthetic Run

```sh
tools/devirt_compare.py --no-default-external
```

This runs the default SMACK and SeaDsa variants on small in-repo C fixtures and
writes:

- `build/devirt-compare/devirt-comparison.json`
- `build/devirt-compare/devirt-comparison.md`

## Full External Run

Install SVF and PhASAR locally, or put one of the default tool names on `PATH`:

- SVF local resolver: `svf-devirt-oracle` or `svf-local-devirt`
- PhASAR: `phasar-cli`, `phasar-llvm`, or `phasar`

Local install:

```sh
python3 -m pip install --prefix build/devirt-analyzers/cmake-prefix 'cmake>=3.29,<3.31'
tools/install_devirt_analyzers.py \
  --cmake tools/cmake_prefix_wrapper.py \
  --svf-llvm-config /usr/lib/llvm-14/bin/llvm-config \
  --phasar-llvm-config /usr/lib/llvm-22/bin/llvm-config
```

This writes `build/devirt-analyzers/manifest.json` with the discovered tool
paths, source refs, commits, LLVM version, build commands, and any build
errors. In this workspace SVF is built against LLVM 14 because `SVF-3.2` does
not compile against LLVM 22, while PhASAR is built against LLVM 22. The
comparison harness consumes that manifest directly:

Then run:

```sh
tools/devirt_compare.py --analyzer-manifest build/devirt-analyzers/manifest.json
```

The default SVF candidate is `svf-local-ander`, which queries SVF Andersen
points-to sets for the loaded vtable/base pointer and then applies the same
local slot extraction used by SMACK. Raw SVF comparison candidates are still
available with `wpa ... -print-fp`. Labels select the SVF mode:
`svf-ander`, `svf-sander`, `svf-sfrander`, `svf-steens`, `svf-fspta`,
`svf-vfspta`, and `svf-type` map to the corresponding WPA flags. Labels may
also include `model-arrays`, `model-consts`, `pre-field`, or `vt-in-ir`; for
example, `svf-local-ander-model-arrays=svf-devirt-oracle,svf-local-devirt`
runs the local resolver with `-ander -model-arrays`.
The PhASAR adapter invokes VTA call graph construction and also reads
`results.json` when PhASAR emits it. External candidate failures are reported
in the comparison output and make the command exit non-zero unless
`--allow-external-failures` is set.

## BearSSL Benchmark

BearSSL is not vendored or fetched by default. Build linked bitcode from a local
checkout:

```sh
tools/build_bearssl_bitcode.py --bearssl-source /path/to/BearSSL
tools/devirt_compare.py \
  --analyzer-manifest build/devirt-analyzers/manifest.json \
  --bearssl-bc build/devirt-bearssl/bearssl-linked.bc \
  --external-input svf:bearssl=build/devirt-bearssl-llvm14/bearssl-linked.bc
```

The generated driver exposes `bearssl_devirt_entry` and intentionally exercises
BearSSL hash, AES CBC/CTR, and SSL vtable-style dispatch so indirect-call
target sets are visible to the comparison. The comparison harness has an
expected-target oracle for the eight synthetic driver callsites and reports
oracle soundness, exactness, missing targets, and spurious targets for those
callsites. If an external analyzer needs bitcode or LLVM IR from a different
LLVM toolchain, provide an override:

```sh
tools/devirt_compare.py \
  --bearssl-bc build/devirt-bearssl/bearssl-linked.bc \
  --external-input svf:bearssl=/path/to/svf-compatible-bearssl.bc \
  --external-input phasar:bearssl=/path/to/phasar-compatible-bearssl.ll
```

To compare several SVF modes on BearSSL:

```sh
tools/devirt_compare.py \
  --analyzer-manifest build/devirt-analyzers/manifest.json \
  --bearssl-bc build/devirt-bearssl/bearssl-linked.bc \
  --external-input svf:bearssl=build/devirt-bearssl-llvm14/bearssl-linked.bc \
  --external-candidate svf-local-ander-model-arrays=svf-devirt-oracle,svf-local-devirt \
  --external-candidate svf-ander=wpa,svf-ex \
  --external-candidate svf-sfrander=wpa,svf-ex \
  --external-candidate svf-ander-model-arrays=wpa,svf-ex \
  --external-candidate svf-fspta=wpa,svf-ex
```

## Custom Reports

An external canonical report can be compared without running an analyzer:

```sh
tools/devirt_compare.py \
  --no-default-external \
  --external-candidate custom=json:/path/to/devirt-report.json
```

The report must use the same `callsites` shape as `-smack-devirt-report`.

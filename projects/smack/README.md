# OSS-Fuzz project skeleton

This directory mirrors the layout that upstream OSS-Fuzz expects at
`projects/smack/` in https://github.com/google/oss-fuzz. We keep it in
the SMACK repo so contributors can reproduce the OSS-Fuzz build
environment locally, and so the eventual upstream PR is a copy not a
write-from-scratch.

## Files

| File          | Role                                                  |
|---------------|--------------------------------------------------------|
| `Dockerfile`  | Build environment for the OSS-Fuzz worker.             |
| `build.sh`    | Compiles fuzzers + drops them at `$OUT/`.              |
| `project.yaml`| OSS-Fuzz metadata (language, sanitizers, contacts).    |

## Upstreaming

1. File project application: https://google.github.io/oss-fuzz/getting-started/new-project-guide/
2. Once approved, mirror this directory into the OSS-Fuzz repo via PR.
3. Update `auto_ccs` + `primary_contact` in `project.yaml` to the
   addresses that should receive crash reports.

## Local reproduction

```bash
git clone https://github.com/google/oss-fuzz.git /tmp/oss-fuzz
cp -r projects/smack /tmp/oss-fuzz/projects/
cd /tmp/oss-fuzz
python infra/helper.py build_image smack
python infra/helper.py build_fuzzers --sanitizer address smack
python infra/helper.py run_fuzzer smack fuzz_bitcode_parse
```

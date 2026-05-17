#!/usr/bin/env bash
# Verify each submodule's current SHA matches tools/submodule-pins.txt.
# Run from the repo root.
set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
PIN_FILE="$REPO_ROOT/tools/submodule-pins.txt"

if [[ ! -f "$PIN_FILE" ]]; then
  echo "error: $PIN_FILE missing" >&2
  exit 2
fi

declare -A expected
while read -r sha path; do
  [[ -z "$sha" || "$sha" == \#* ]] && continue
  expected["$path"]="$sha"
done < "$PIN_FILE"

status=0
while read -r flag_sha path _rest; do
  # `git submodule status` lines look like:
  #   " <sha> <path> (describe)"   when clean
  #   "+<sha> <path> (describe)"   when checked out at a different commit
  #   "-<sha> <path>"              when not initialized
  # `read` already split on whitespace; trim optional status prefix from sha.
  actual_sha="${flag_sha#[-+U]}"

  exp="${expected[$path]:-}"
  if [[ -z "$exp" ]]; then
    echo "FAIL: $path checked out @ $actual_sha but not listed in submodule-pins.txt"
    status=1
    continue
  fi
  if [[ "$exp" != "$actual_sha" ]]; then
    echo "FAIL: $path expected $exp but found $actual_sha"
    status=1
  fi
done < <(git -C "$REPO_ROOT" submodule status)

if [[ $status -eq 0 ]]; then
  echo "OK: all submodule SHAs match pins"
fi
exit "$status"

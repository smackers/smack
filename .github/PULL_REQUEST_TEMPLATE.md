<!-- Title (above): use a Conventional Commit prefix.
     feat / fix / refactor / docs / test / ci / perf / build / chore
     A breaking change uses `feat!:` or includes a `BREAKING CHANGE:` footer. -->

## What
<!-- One paragraph. What does this PR change and why? -->

## How
<!-- The shape of the change. Files touched, key decisions, anything
     a reviewer would otherwise have to reverse-engineer. -->

## Verification
<!-- Mark the checks you actually ran. Don't tick a box if you didn't run it. -->

- [ ] `cmake --build build && ctest --test-dir build` (C++ unit tests)
- [ ] `pytest test/python -q -m "not slow"` (Python fast gate)
- [ ] `python3 test/regtest.py --exhaustive --folder=<relevant>` (regtest smoke)
- [ ] `pre-commit run --all-files`
- [ ] CodeQL + sanitizer jobs green on the PR

## Risk

<!-- Pick one. If non-trivial, expand. -->
- [ ] Low — additive, no behavior change
- [ ] Medium — behavior change in a single subsystem
- [ ] High — touches translator soundness, build system, or sea-dsa bridge

## Out of scope
<!-- Anything intentionally NOT addressed by this PR. -->

---
<!-- Reviewer hints -->
Related issues: <!-- #123, none -->
Cross-repo coordination needed: <!-- yes/no -->

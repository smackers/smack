# Security Policy

## Supported Versions

| Version | Supported          |
| ------- | ------------------ |
| 2.8.x   | ✅                 |
| < 2.8   | ❌ (please upgrade) |

The fork on this repository tracks the SMACK 2.8 line on LLVM 22. Older
SMACK releases (LLVM ≤ 15) are out of scope.

## Reporting a Vulnerability

If you find a security vulnerability in SMACK — for example a memory-safety
bug in the C++ translator, an injection vector in the Python driver,
verification soundness gaps that could let an unsafe program be proven
safe, or supply-chain risk in our build/CI — please report it privately.

**Do not** open a public GitHub issue.

Preferred channel:

- GitHub Security Advisories — open a draft advisory on this repo via
  `Security` → `Report a vulnerability`.

Fallback channel:

- Email the maintainers listed in `README.md` (Zvonimir, Michael, Shaobo).
  Encrypt sensitive details if possible.

Include in the report:

- A description of the issue and its impact.
- Reproduction steps or a proof-of-concept input.
- The SMACK commit, LLVM version (`llvm-config --version`), and OS.
- Any suggested mitigation if you have one.

## Disclosure timeline

- Acknowledgement within **7 days** of report receipt.
- Triage + severity assessment within **30 days**.
- Coordinated public disclosure once a fix is available, with credit to
  the reporter unless they prefer anonymity.

## Scope

In scope:

- C++ translator (`lib/smack`, `include/smack`, `tools/`).
- Python driver (`share/smack/`, `bin/smack`).
- Build/CI infrastructure (`bin/build.sh`, `.github/workflows/`,
  `Dockerfile`).
- Soundness bugs in the LLVM → Boogie translation that affect what
  programs verifiers can prove.

Out of scope (report upstream instead):

- Vulnerabilities in `sea-dsa` → https://github.com/seahorn/sea-dsa
- Vulnerabilities in LLVM, Clang, Boogie, Corral, Z3, dotnet itself.
- Tool-chain issues in vendored Rust toolchain.

## Hardening you can rely on

- CodeQL (cpp + python) runs on every PR and weekly via
  `.github/workflows/codeql.yml`.
- ASan + UBSan smoke runs on every PR via the `cpp-sanitizers` job in
  `.github/workflows/smack-ci.yaml`.
- Submodule SHAs are pinned and enforced by
  `tools/check_submodule_pins.sh` (CI gate + pre-commit hook).
- Release artifacts include a CycloneDX SBOM and SLSA build provenance
  attestation; see `.github/workflows/release.yml`.
- PyPI publishes use trusted-publishing (no long-lived API tokens in
  GitHub secrets).

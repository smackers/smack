"""Pytest wrapper around test/regtest.py.

The 452-LOC regtest.py runs SMACK regressions per folder with a hand-rolled
ThreadPool harness. This wrapper exposes those per-folder invocations as
pytest test functions so we get:

  - JUnit XML output for CI dashboards (`--junitxml`)
  - pytest-xdist parallelism across folders (`pytest -n auto`)
  - Test selection by name (`pytest -k 'memory_safety or basic'`)
  - Configurable timeouts and markers
  - Native skip/xfail support

We intentionally do **not** reimplement the regtest internals — those
stay in regtest.py until the eventual Phase 4.1 full rewrite. The
wrapper simply shells out per folder and propagates pass/fail.

Each test is marked ``regtest`` and ``slow`` so the existing
``-m "not slow"`` fast gate keeps skipping it. CI's ``check-regressions``
job runs these explicitly with ``pytest -m regtest``.

Skip the whole module unless ``SMACK_RUN_REGTEST=1`` is set, since these
tests need a built SMACK toolchain on ``$PATH`` plus dotnet/boogie/corral
that aren't available in fast CI shards.
"""

from __future__ import annotations

import os
import shlex
import subprocess
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
REGTEST_SCRIPT = REPO_ROOT / "test" / "regtest.py"

# Per-folder spec mirrors the matrix in .github/workflows/smack-ci.yaml.
# (folder, languages, extra_flags). When the CI matrix changes, mirror here.
REGTEST_MATRIX: list[tuple[str, str | None, list[str]]] = [
    ("c/basic", None, []),
    ("c/data", None, []),
    ("c/ntdrivers-simplified", None, []),
    ("c/ntdrivers", None, []),
    ("c/bits", None, []),
    ("c/float", None, []),
    ("c/locks", None, []),
    ("c/contracts", None, []),
    ("c/simd", None, []),
    ("c/memory-safety", None, []),
    ("c/pthread", None, []),
    ("c/pthread_extras", None, []),
    ("c/strings", None, []),
    ("c/special", None, []),
    ("c/targeted-checks", None, []),
    ("c/unroll", None, []),
    ("rust/array", "rust", []),
    ("rust/basic", "rust", []),
    ("rust/box", "rust", []),
    ("rust/functions", "rust", []),
    ("rust/generics", "rust", []),
    ("rust/loops", "rust", []),
    ("rust/panic", "rust", []),
    ("rust/recursion", "rust", []),
    ("rust/structures", "rust", []),
    ("rust/targeted-checks", None, []),
    ("rust/vector", "rust", []),
    ("rust/cargo/**", "cargo", ["--threads=1"]),
    ("llvm", "llvm-ir", []),
]


_needs_toolchain = pytest.mark.skipif(
    os.environ.get("SMACK_RUN_REGTEST") != "1",
    reason="SMACK_RUN_REGTEST=1 not set; regtest needs a built SMACK toolchain.",
)


def _id_for(spec: tuple[str, str | None, list[str]]) -> str:
    folder, lang, flags = spec
    parts = [folder.replace("/", "_").replace("**", "all")]
    if lang:
        parts.append(lang)
    if flags:
        parts.append("flags=" + ",".join(flags))
    return "-".join(parts)


@pytest.mark.regtest
@pytest.mark.slow
@_needs_toolchain
@pytest.mark.parametrize("spec", REGTEST_MATRIX, ids=_id_for)
def test_regtest_folder(spec: tuple[str, str | None, list[str]], tmp_path: Path) -> None:
    folder, lang, extra_flags = spec
    output_dir = tmp_path / "output"
    output_dir.mkdir(parents=True, exist_ok=True)

    cmd: list[str] = [
        sys.executable,
        str(REGTEST_SCRIPT),
        "--exhaustive",
        f"--folder={folder}",
        f"--output-dir={output_dir}",
    ]
    if lang:
        cmd.append(f"--languages={lang}")
    cmd.extend(extra_flags)

    # Per-folder timeout: 30 min hard ceiling. Individual test cases have
    # their own time-limits set in their YAML configs.
    timeout = int(os.environ.get("SMACK_REGTEST_FOLDER_TIMEOUT", "1800"))

    proc = subprocess.run(
        cmd,
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        timeout=timeout,
        check=False,
    )

    if proc.returncode != 0:
        pytest.fail(
            f"regtest.py failed (rc={proc.returncode}) for {shlex.join(cmd)}\n"
            f"--- stdout ---\n{proc.stdout[-8000:]}\n--- stderr ---\n{proc.stderr[-4000:]}"
        )


def test_regtest_matrix_matches_ci() -> None:
    """Smoke check: the matrix used here lines up with the CI workflow.

    Drift between the wrapper matrix and the GitHub Actions matrix means CI
    coverage diverges from local pytest runs. Failing this test forces us
    to update both in lockstep.
    """
    ci_yaml = REPO_ROOT / ".github" / "workflows" / "smack-ci.yaml"
    text = ci_yaml.read_text()
    # Spot-check: every folder in REGTEST_MATRIX appears in the CI yaml.
    missing = [f for f, _, _ in REGTEST_MATRIX if f"--folder={f}" not in text]
    assert not missing, f"CI workflow missing folders covered by pytest matrix: {missing}"

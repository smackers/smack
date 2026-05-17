"""CLI smoke tests for `bin/smack`.

Validate that the post-decomposition top.py re-exports keep `bin/smack` working
end-to-end (`--version`, `--help`) and that every documented re-export name is
still importable from `smack.top`.

These tests do NOT invoke clang/boogie/z3 — pure CLI introspection. Cheap to
run in CI; first line of defense against regressions in the B5 sub-module
extraction.
"""

import importlib
import re
import subprocess
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
SMACK_BIN = REPO_ROOT / "bin" / "smack"

# Re-exports that must keep resolving from `smack.top` after Phase B5.
# Grouped by source sub-module so test failures point at the right extract.
REEXPORTS = {
    "smack.cli.results": ["VResult", "VProperty", "PropertyAction"],
    "smack.cli.parser": [
        "FileAction",
        "arguments",
        "exit_with_error",
        "validate_input_files",
        "validate_output_file",
    ],
    "smack.constants": ["VERSION", "inlined_procedures"],
    "smack.verifier.commands": [
        "boogie_command",
        "corral_command",
    ],
    "smack.verifier.runner": [
        "process_verifier_output",
        "verification_result",
        "verify_bpl",
    ],
    "smack.verifier.portfolio": ["thread_verify_bpl", "verify_bpl_portfolio"],
    "smack.pipeline.frontend": ["frontend", "target_selection"],
    "smack.pipeline.transform": ["transform_bpl", "transform_out"],
    "smack.pipeline.translate": [
        "annotate_bpl",
        "memsafety_subproperty_selection",
        "procedure_annotation",
        "replace_reach_error",
    ],
    "smack.diffprod.orchestrate": [
        "diff_product_patched_filename",
        "diff_product_side_args",
        "llvm_to_bpl_option_args",
        "run_diff_product",
        "run_paired_diff_product_lowering",
        "verify_diff_product",
    ],
}


def _run_smack(*args, timeout=30):
    return subprocess.run(
        [sys.executable, str(SMACK_BIN), *args],
        capture_output=True,
        text=True,
        timeout=timeout,
    )


def test_smack_binary_exists():
    assert SMACK_BIN.exists(), f"missing {SMACK_BIN}"


def test_version_string_matches_constant():
    result = _run_smack("--version")
    assert result.returncode == 0, result.stderr
    assert "2.8.0" in (result.stdout + result.stderr)
    assert "SMACK version" in (result.stdout + result.stderr)


def test_help_lists_core_flags():
    result = _run_smack("--help")
    assert result.returncode == 0, result.stderr
    out = result.stdout + result.stderr
    for flag in [
        "--check",
        "--verifier",
        "--unroll",
        "--no-verify",
        "--bpl-file",
        "--diff-product",
        "--sea-dsa-mode",
        "--memory-partitioner",
        "--memory-partition-oracle",
        "--svf-wpa",
        "--svf-extapi",
        "--svf-mem-par",
        "--svf-timeout",
        "--memory-partition-report",
        "--devirt-report",
    ]:
        assert flag in out, f"--help missing flag {flag}"


def test_main_callable():
    from smack.top import main

    assert callable(main)


@pytest.mark.parametrize(
    "source_module,names",
    [(mod, names) for mod, names in REEXPORTS.items()],
    ids=list(REEXPORTS.keys()),
)
def test_reexports_resolve_via_smack_top(source_module, names):
    """Every B5-extracted name must remain importable from smack.top."""
    top = importlib.import_module("smack.top")
    for name in names:
        assert hasattr(top, name), f"smack.top.{name} missing after extraction from {source_module}"


@pytest.mark.parametrize(
    "source_module,names",
    [(mod, names) for mod, names in REEXPORTS.items()],
    ids=list(REEXPORTS.keys()),
)
def test_reexport_object_identity_matches_source(source_module, names):
    """The re-export must be the SAME object as in the source sub-module."""
    top = importlib.import_module("smack.top")
    src = importlib.import_module(source_module)
    for name in names:
        assert getattr(top, name) is getattr(
            src, name
        ), f"smack.top.{name} differs from {source_module}.{name}"


def test_version_format():
    from smack.constants import VERSION

    assert re.match(r"^\d+\.\d+\.\d+$", VERSION), f"VERSION={VERSION!r} not semver"


def test_inlined_procedures_shape():
    from smack.constants import inlined_procedures

    procs = inlined_procedures()
    assert isinstance(procs, list)
    assert len(procs) > 0
    for p in procs:
        assert p.startswith("$") or p.startswith(
            "__"
        ), f"inlined procedure {p!r} doesn't follow $ or __ convention"


def test_smack_help_includes_diffprod_mode_choices():
    result = _run_smack("--help")
    out = result.stdout + result.stderr
    # diffprod orchestration sub-module must wire --product-mode choices
    assert "--product-mode" in out
    assert "functions" in out
    assert "patch" in out

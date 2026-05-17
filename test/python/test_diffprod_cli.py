import json
import os
import shutil
import subprocess
from pathlib import Path

import pytest
from smack_test_paths import diff_product_cli, run_with_timeout, tool_path, tool_path_env


def assert_boogie_verifies(path):
    boogie = shutil.which("boogie")
    if boogie is None:
        pytest.skip("boogie executable not found")
    completed = run_with_timeout(
        [boogie, str(path)],
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        check=False,
        timeout_name="BOOGIE",
        default_timeout=60,
    )
    assert "Error:" not in completed.stdout
    assert "0 errors" in completed.stdout


def run_cli_case(tmp_path, name, extra_args):
    left = tmp_path / f"{name}_left.c"
    right = tmp_path / f"{name}_right.c"
    diff = tmp_path / f"{name}.diff"
    product = tmp_path / f"{name}.bpl"
    report = tmp_path / f"{name}.json"
    left.write_text("int f(int x) {\n  return x + 0;\n}\n")
    right.write_text("int f(int x) {\n  return x - 0;\n}\n")
    diff.write_text(
        "\n".join(
            [
                f"--- a/{left.name}",
                f"+++ b/{right.name}",
                "@@ -2,1 +2,1 @@",
                "-  return x + 0;",
                "+  return x - 0;",
            ]
        )
        + "\n"
    )
    env = tool_path_env()
    completed = run_with_timeout(
        [
            diff_product_cli(),
            "--quiet",
            "--diff-product",
            str(diff),
            "--diff-left",
            str(left),
            "--diff-right",
            str(right),
            "--diff-left-entry",
            "f",
            "--diff-right-entry",
            "f",
            "--diff-product-out",
            str(product),
            "--diff-product-json",
            str(report),
            *extra_args,
        ],
        cwd=tmp_path,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        check=False,
        env=env,
        timeout_name="SMACK",
        default_timeout=180,
    )
    assert completed.returncode == 0, completed.stdout
    assert product.exists()
    assert report.exists()
    return product, json.loads(report.read_text())


def run_easy_cli_case(tmp_path, name, mode):
    left = tmp_path / f"{name}_left.c"
    right = tmp_path / f"{name}_right.c"
    diff = tmp_path / f"{name}.diff"
    product = tmp_path / f"{name}.bpl"
    report = tmp_path / f"{name}.json"
    left.write_text("int f(int x) {\n  return x + 0;\n}\n")
    right.write_text("int f(int x) {\n  return x - 0;\n}\n")
    diff.write_text(
        "\n".join(
            [
                f"--- a/{left.name}",
                f"+++ b/{right.name}",
                "@@ -2,1 +2,1 @@",
                "-  return x + 0;",
                "+  return x - 0;",
            ]
        )
        + "\n"
    )
    env = tool_path_env()
    if mode == "functions":
        mode_args = [
            "--product-mode",
            "functions",
            "--left",
            str(left),
            "--right",
            str(right),
        ]
    else:
        mode_args = [
            "--product-mode",
            "patch",
            "--source",
            str(left),
            "--patch",
            str(diff),
        ]
    completed = run_with_timeout(
        [
            diff_product_cli(),
            "--quiet",
            *mode_args,
            "--entry",
            "f",
            "--product-out",
            str(product),
            "--product-json",
            str(report),
        ],
        cwd=tmp_path,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        check=False,
        env=env,
        timeout_name="SMACK",
        default_timeout=180,
    )
    assert completed.returncode == 0, completed.stdout
    assert product.exists()
    assert report.exists()
    return product, json.loads(report.read_text())


@pytest.mark.slow
def test_diff_product_cli_writes_product_and_json_for_alignment_modes(tmp_path):
    product, report = run_cli_case(
        tmp_path,
        "auto",
        [],
    )
    assert report["product"]["actual_product_available"] is True
    assert report["product"]["selection"]
    assert any(candidate["selected"] for candidate in report["product"]["selection"])
    assert report["equivalence"]["checked"] is False
    assert_boogie_verifies(product)

    product, report = run_cli_case(
        tmp_path,
        "legacy_no_egraph",
        ["--diff-product-alignment", "legacy", "--diff-product-no-egraph"],
    )
    assert report["product"]["actual_product_available"] is True
    assert report["product"]["mode"] == "legacy"
    assert report["product"]["egraph_success"] is False
    assert report["product"]["egraph_outcomes"] == []
    assert report["impact"]["left"]["impacted_blocks"]
    assert report["summaries"]["left"] is not None
    assert report["failure_cut"]
    assert_boogie_verifies(product)

    product, report = run_cli_case(
        tmp_path,
        "baseline",
        ["--diff-product-alignment", "baseline"],
    )
    assert report["product"]["actual_product_available"] is True
    assert report["product"]["mode"] == "baseline"
    assert report["product"]["lockstep_outcomes"] == []
    assert report["product"]["egraph_outcomes"] == []
    assert_boogie_verifies(product)


def test_easy_product_mode_functions_uses_llvm_matcher_alignment(tmp_path):
    product, report = run_easy_cli_case(tmp_path, "functions", "functions")

    assert report["product"]["actual_product_available"] is True
    assert any("interface mode: functions" in d for d in report["diagnostics"])
    assert report["llvm_match"]
    assert report["llvm_match"]["source"] == "smack-cpp"
    assert report["llvm_match"]["stats"]["matcher_ms"] >= 0
    assert report["llvm_match"]["chunks"]
    assert report["product"]["selection"]
    assert_boogie_verifies(product)


def test_easy_product_mode_patch_materializes_right_source(tmp_path):
    product, report = run_easy_cli_case(tmp_path, "patch", "patch")

    assert report["product"]["actual_product_available"] is True
    assert any("interface mode: patch" in d for d in report["diagnostics"])
    assert report["llvm_match"]["source"] == "smack-cpp"
    assert report["impact"]["left"]["impacted_blocks"]
    assert report["impact"]["right"]["impacted_blocks"]
    assert_boogie_verifies(product)


def test_product_mode_requires_smack_cpp_matcher(tmp_path):
    left = tmp_path / "missing_tool_left.c"
    right = tmp_path / "missing_tool_right.c"
    product = tmp_path / "missing_tool.bpl"
    left.write_text("int f(int x) {\n  return x + 0;\n}\n")
    right.write_text("int f(int x) {\n  return x - 0;\n}\n")

    env = tool_path_env()
    tool_dir = tmp_path / "tools"
    tool_dir.mkdir()
    for tool in ("extern-statics", "llvm2bpl"):
        os.symlink(Path(tool_path(tool)), tool_dir / tool)
    env["PATH"] = os.pathsep.join([str(tool_dir), "/usr/lib/llvm-22/bin", "/usr/bin", "/bin"])

    completed = run_with_timeout(
        [
            diff_product_cli(),
            "--quiet",
            "--product-mode",
            "functions",
            "--left",
            str(left),
            "--right",
            str(right),
            "--entry",
            "f",
            "--product-out",
            str(product),
        ],
        cwd=tmp_path,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        check=False,
        env=env,
        timeout_name="SMACK",
        default_timeout=180,
    )

    assert completed.returncode != 0
    assert "llvm-diffmatch2bpl" in completed.stdout
    assert "on PATH" in completed.stdout

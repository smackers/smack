# ruff: noqa: E501

import difflib
import json
import re
import shutil
import subprocess

import pytest
from smack.diffprod.diff import parse_unified_diff
from smack.diffprod.pipeline import build_from_bpl
from smack.diffprod.provenance import parse_boogie_with_provenance
from smack_test_paths import diff_product_cli, run_with_timeout, tool_path_env

LEFT_BPL = """
procedure main();
implementation main()
{
  var x: int;

entry:
  assume {:sourceloc "demo.c" 2 1} {:c_line "x = 0;"} {:llvm.func "main"} {:llvm.bb "entry"} {:llvm.inst "main:entry:0"} {:llvm.op "store"} true;
  x := 0;
  goto exit;

stable:
  assume {:sourceloc "demo.c" 10 1} {:llvm.func "main"} {:llvm.bb "stable"} {:llvm.inst "main:stable:0"} {:llvm.op "add"} true;
  assume true;
  return;

exit:
  assert x >= 0;
  return;
}
"""

RIGHT_BPL = LEFT_BPL.replace('x = 0;', 'x = 1;').replace('x := 0;', 'x := 1;')

PATCH = """--- a/demo.c
+++ b/demo.c
@@ -2,1 +2,1 @@
-x = 0;
+x = 1;
"""


def smack_executable():
    return diff_product_cli()


def write_smack_bpl(tmp_path, name, source, entry="f"):
    src = tmp_path / f"{name}.c"
    bpl = tmp_path / f"{name}.bpl"
    src.write_text(source)
    run_with_timeout(
        [smack_executable(), "-t", "--entry-points", entry, "-bpl", str(bpl), str(src)],
        cwd=tmp_path,
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        env=tool_path_env(),
        timeout_name="SMACK",
        default_timeout=180,
    )
    return bpl


def assert_boogie_verifies(path, *extra_args):
    boogie = shutil.which("boogie")
    if boogie is None:
        pytest.skip("boogie executable not found")
    completed = run_with_timeout(
        [boogie, *extra_args, str(path)],
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        check=False,
        timeout_name="BOOGIE",
        default_timeout=60,
    )
    assert "Error:" not in completed.stdout
    assert "0 errors" in completed.stdout


def assert_boogie_rejects(path, *extra_args):
    boogie = shutil.which("boogie")
    if boogie is None:
        pytest.skip("boogie executable not found")
    completed = run_with_timeout(
        [boogie, *extra_args, str(path)],
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        check=False,
        timeout_name="BOOGIE",
        default_timeout=60,
    )
    assert "0 errors" not in completed.stdout


def build_smack_product(
    tmp_path,
    name,
    left_source,
    right_source,
    diff_text,
    *,
    alignment="legacy",
    no_egraph=False,
):
    left_bpl = write_smack_bpl(tmp_path, f"{name}_left", left_source)
    right_bpl = write_smack_bpl(tmp_path, f"{name}_right", right_source)
    result = build_from_bpl(
        left_bpl=left_bpl.read_text(),
        right_bpl=right_bpl.read_text(),
        diff_text=diff_text,
        left_entry="f",
        right_entry="f",
        alignment=alignment,
        no_egraph=no_egraph,
    )
    product = tmp_path / f"{name}_product.bpl"
    product.write_text(result.product.text)
    return result, product


def run_product_with_interpreter(product_text, tmp_path, name, inputs):
    pytest.importorskip("swoosh_interp")
    from interpreter.parser.boogie_parser import parse_boogie
    from interpreter.runner import run_native
    from interpreter.utils.inputs import Input, ProgramInputs

    text = re.sub(
        r"\bimplementation\s+([A-Za-z_$][A-Za-z0-9_.$]*)\(",
        r"implementation {:entrypoint} \1(",
        product_text,
        count=1,
    )
    program_inputs = ProgramInputs(
        {var: Input(name=var, private=False, value=value) for var, value in inputs.items()}
    )
    try:
        return run_native(
            parse_boogie(text),
            program_inputs,
            test_name=name,
            input_name=name,
            raw_log_path=tmp_path / f"{name}.trace.raw.zst",
            no_trace=True,
            log_read=False,
            return_status=True,
            return_scalar_summary=True,
        )
    except RuntimeError as exc:
        if "return_scalar_summary" in str(exc):
            pytest.skip(str(exc))
        raise


def source_diff(name, left, right):
    return "".join(
        difflib.unified_diff(
            left.splitlines(keepends=True),
            right.splitlines(keepends=True),
            fromfile=f"{name}_left.c",
            tofile=f"{name}_right.c",
            n=2,
        )
    )


def assert_product_naming_invariants(result):
    assert result.product.actual_product_available is True
    assert result.product.actual_source == "diffprod-product-v2"
    assert ".P:" in result.product.text
    assert ".Q:" in result.product.text
    assert "P_$bb" not in result.product.text
    assert "Q_$bb" not in result.product.text
    assert "$r_P" not in result.product.text
    assert "$r_Q" not in result.product.text


def assert_product_core_invariants(result):
    assert_product_naming_invariants(result)
    report = result.to_json()["product"]
    json.dumps(result.to_json())
    assert report["selection"]
    assert sum(1 for candidate in report["selection"] if candidate["selected"]) == 1
    assert report["egraph_outcomes"]
    for outcome in report["egraph_outcomes"]:
        assert outcome["debug_steps"], outcome
    assert_egraph_regions_are_delta_scoped(report)
    return report


def assert_egraph_success_with_debug(report):
    successes = [
        outcome
        for outcome in report["egraph_outcomes"]
        if outcome["success"] and outcome["resolution"].startswith("egraph")
    ]
    assert successes
    phases = {step["phase"] for outcome in successes for step in outcome["debug_steps"]}
    assert phases
    return successes


def assert_egraph_regions_are_delta_scoped(report):
    left_delta = {f"{block}.P" for block in report["delta"]["left_blocks"]}
    right_delta = {f"{block}.Q" for block in report["delta"]["right_blocks"]}
    assert left_delta or right_delta
    for outcome in report["egraph_outcomes"]:
        left_region = set(outcome["region"]["left_blocks"])
        right_region = set(outcome["region"]["right_blocks"])
        assert left_region <= left_delta, outcome
        assert right_region <= right_delta, outcome


def assert_impact_has_reason(result, side, reason):
    impact = result.to_json()["impact"][side]
    assert any(
        entry["reason"] == reason for entries in impact["reasons"].values() for entry in entries
    )


def assert_egraph_reports_non_assignment_region(report):
    assert any(
        step.get("reason") == "region contains non-assignment statements"
        for outcome in report["egraph_outcomes"]
        for step in outcome["debug_steps"]
    )


def assert_egraph_step_comments_match_report(result):
    report = result.to_json()["product"]
    expected = sum(len(outcome["debug_steps"]) for outcome in report["egraph_outcomes"])
    actual = sum(
        1
        for line in result.product.text.splitlines()
        if line.startswith("// diffprod.egraph.step ")
    )
    assert actual == expected


def test_parse_unified_diff_hunks():
    hunks = parse_unified_diff(PATCH)
    assert len(hunks) == 1
    assert hunks[0].old_path == "demo.c"
    assert hunks[0].new_start == 2


def test_parse_unified_diff_edge_hunks():
    hunks = parse_unified_diff(
        "\n".join(
            [
                "--- a/demo.c",
                "+++ b/demo.c",
                "@@ -2,0 +3,1 @@",
                "+inserted();",
                "@@ -5,1 +6,0 @@",
                "-deleted();",
                "--- /dev/null",
                "+++ b/new.c",
                "@@ -0,0 +1,1 @@",
                "+created();",
            ]
        )
        + "\n"
    )

    assert [(h.old_len, h.new_len) for h in hunks] == [(0, 1), (1, 0), (0, 1)]
    assert hunks[2].old_path is None
    assert hunks[2].new_path == "new.c"


def test_parse_unified_diff_ignores_whitespace_only_hunks():
    hunks = parse_unified_diff(
        "\n".join(
            [
                "--- a/demo.c",
                "+++ b/demo.c",
                "@@ -2,1 +2,1 @@",
                "-  x = 0;",
                "+  x = 0;  ",
            ]
        )
        + "\n"
    )

    assert hunks == []


def test_parse_smack_space_separated_provenance_attrs():
    parsed = parse_boogie_with_provenance(LEFT_BPL)
    stmt_id = "proc:main:block:entry:stmt:0"
    origin = parsed.provenance.origin_set(stmt_id).records[0]
    assert origin.source_span.file == "demo.c"
    assert origin.source_span.start_line == 2
    assert origin.llvm_inst_id == "main:entry:0"
    assert "normalized SMACK attribute syntax before parsing" in parsed.diagnostics


def test_source_diff_closes_over_cfg_and_data_dependencies():
    result = build_from_bpl(
        left_bpl=LEFT_BPL,
        right_bpl=RIGHT_BPL,
        diff_text=PATCH,
        left_entry="main",
        right_entry="main",
    )
    impacted = result.impact.left.impacted_blocks
    assert "proc:main:block:entry" in impacted
    assert "proc:main:block:exit" in impacted
    assert "x" in result.impact.left.variables


def test_multiple_diff_seeds_do_not_swallow_independent_stable_blocks():
    left = """
procedure main(y: int) returns (r: int);
implementation main(y: int) returns (r: int)
{
  var x: int;
  var z: int;
  var stable: int;

entry:
  assume {:sourceloc "demo.c" 2 1} {:c_line "x = 0;"} true;
  x := 0;
  goto stable_block;

stable_block:
  assume {:sourceloc "demo.c" 20 1} {:c_line "stable = y + 1;"} true;
  stable := y + 1;
  goto late;

late:
  assume {:sourceloc "demo.c" 4 1} {:c_line "z = 0;"} true;
  z := 0;
  goto exit;

exit:
  r := x + z;
  return;
}
"""
    right = left.replace('x = 0;', 'x = 1;').replace('x := 0;', 'x := 1;')
    right = right.replace('z = 0;', 'z = 1;').replace('z := 0;', 'z := 1;')
    result = build_from_bpl(
        left_bpl=left,
        right_bpl=right,
        diff_text="\n".join(
            [
                "--- a/demo.c",
                "+++ b/demo.c",
                "@@ -2,1 +2,1 @@",
                "-x = 0;",
                "+x = 1;",
                "@@ -4,1 +4,1 @@",
                "-z = 0;",
                "+z = 1;",
            ]
        )
        + "\n",
        left_entry="main",
        right_entry="main",
        alignment="legacy",
    )

    impacted = result.impact.left.impacted_blocks
    assert "proc:main:block:entry" in impacted
    assert "proc:main:block:late" in impacted
    assert "proc:main:block:exit" in impacted
    assert "proc:main:block:stable_block" not in impacted
    assert any(
        region.block_id == "proc:main:block:stable_block" for region in result.summaries.left
    )
    assert "stable" not in result.impact.left.variables


def test_unchanged_downstream_branch_is_impacted_by_changed_predicate_value():
    left = """
procedure main() returns (r: int);
implementation main() returns (r: int)
{
  var x: int;
  var y: int;

entry:
  assume {:sourceloc "demo.c" 2 1} {:c_line "x = 0;"} true;
  x := 0;
  goto branch;

branch:
  assume x >= 1;
  goto then_block, else_block;

then_block:
  y := 10;
  goto exit;

else_block:
  y := 20;
  goto exit;

exit:
  r := y;
  return;
}
"""
    right = left.replace('x = 0;', 'x = 1;').replace('x := 0;', 'x := 1;')
    result = build_from_bpl(
        left_bpl=left,
        right_bpl=right,
        diff_text="\n".join(
            [
                "--- a/demo.c",
                "+++ b/demo.c",
                "@@ -2,1 +2,1 @@",
                "-x = 0;",
                "+x = 1;",
            ]
        )
        + "\n",
        left_entry="main",
        right_entry="main",
        alignment="legacy",
    )

    impacted = result.impact.left.impacted_blocks
    assert {
        "proc:main:block:entry",
        "proc:main:block:branch",
        "proc:main:block:then_block",
        "proc:main:block:else_block",
        "proc:main:block:exit",
    } <= impacted
    assert_impact_has_reason(result, "left", "data-dependency")
    assert_impact_has_reason(result, "left", "control-dependency")


def test_unchanged_blocks_are_summarized_and_report_is_jsonable():
    result = build_from_bpl(
        left_bpl=LEFT_BPL,
        right_bpl=RIGHT_BPL,
        diff_text=PATCH,
        left_entry="main",
        right_entry="main",
    )
    assert any(r.block_id == "proc:main:block:stable" for r in result.summaries.left)
    assert "procedure" in result.product.text
    assert result.to_json()["summaries"]["left"]
    json.dumps(result.to_json())


def test_raw_quotes_in_source_line_metadata_are_sanitized():
    bpl = LEFT_BPL.replace(
        '{:c_line "x = 0;"}',
        '{:c_line "__SMACK_code("assume true;");"}',
    )
    parsed = parse_boogie_with_provenance(bpl)
    stmt_id = "proc:main:block:entry:stmt:0"
    assert parsed.provenance.origin_set(stmt_id).records[0].c_line == (
        '__SMACK_code("assume true;");'
    )


def test_boogie_diff_insertion_and_deletion_hunks_seed_impact_points():
    base = """
procedure main() returns (r: int);
implementation main() returns (r: int)
{
  var x: int;

entry:
  assume {:sourceloc "demo.c" 2 1} {:c_line "x = 0;"} {:llvm.func "main"} {:llvm.bb "entry"} {:llvm.inst "main:entry:0"} {:llvm.op "store"} true;
  x := 0;
  assume {:sourceloc "demo.c" 4 1} {:c_line "r = x;"} {:llvm.func "main"} {:llvm.bb "entry"} {:llvm.inst "main:entry:1"} {:llvm.op "ret"} true;
  r := x;
  return;
}
"""
    with_insert = """
procedure main() returns (r: int);
implementation main() returns (r: int)
{
  var x: int;

entry:
  assume {:sourceloc "demo.c" 2 1} {:c_line "x = 0;"} {:llvm.func "main"} {:llvm.bb "entry"} {:llvm.inst "main:entry:0"} {:llvm.op "store"} true;
  x := 0;
  assume {:sourceloc "demo.c" 3 1} {:c_line "x = x + 0;"} {:llvm.func "main"} {:llvm.bb "entry"} {:llvm.inst "main:entry:insert"} {:llvm.op "add"} true;
  x := x + 0;
  assume {:sourceloc "demo.c" 4 1} {:c_line "r = x;"} {:llvm.func "main"} {:llvm.bb "entry"} {:llvm.inst "main:entry:1"} {:llvm.op "ret"} true;
  r := x;
  return;
}
"""
    insertion = build_from_bpl(
        left_bpl=base,
        right_bpl=with_insert,
        diff_text="\n".join(
            [
                "--- a/demo.c",
                "+++ b/demo.c",
                "@@ -2,0 +3,1 @@",
                "+  x = x + 0;",
            ]
        )
        + "\n",
        left_entry="main",
        right_entry="main",
        alignment="legacy",
    )
    deletion = build_from_bpl(
        left_bpl=with_insert,
        right_bpl=base,
        diff_text="\n".join(
            [
                "--- a/demo.c",
                "+++ b/demo.c",
                "@@ -3,1 +2,0 @@",
                "-  x = x + 0;",
            ]
        )
        + "\n",
        left_entry="main",
        right_entry="main",
        alignment="legacy",
    )

    for result in (insertion, deletion):
        report = result.to_json()["product"]
        assert report["delta"]["left_blocks"] == ["entry"]
        assert report["delta"]["right_blocks"] == ["entry"]
        assert_egraph_regions_are_delta_scoped(report)
        assert_impact_has_reason(result, "left", "source-diff")
        assert_impact_has_reason(result, "right", "source-diff")


def test_boogie_multifile_diff_ignores_unrelated_file_hunks():
    result = build_from_bpl(
        left_bpl=LEFT_BPL,
        right_bpl=LEFT_BPL,
        diff_text="\n".join(
            [
                "--- a/unrelated.c",
                "+++ b/unrelated.c",
                "@@ -1,1 +1,1 @@",
                "-int g(void) { return 0; }",
                "+int g(void) { return 1; }",
            ]
        )
        + "\n",
        left_entry="main",
        right_entry="main",
        alignment="legacy",
    )

    report = result.to_json()["product"]
    assert result.impact.left.impacted_blocks == set()
    assert result.impact.right.impacted_blocks == set()
    assert report["delta"]["left_blocks"] == []
    assert report["delta"]["right_blocks"] == []
    assert report["egraph_outcomes"] == []
    assert result.to_json()["summaries"]["left"]


def test_boogie_missing_source_provenance_impacts_all_blocks():
    bpl = """
procedure main() returns (r: int);
implementation main() returns (r: int)
{
  var x: int;
entry:
  x := 0;
  goto exit;
exit:
  r := x;
  return;
}
"""
    result = build_from_bpl(
        left_bpl=bpl,
        right_bpl=bpl,
        diff_text="\n".join(
            [
                "--- a/no_provenance.c",
                "+++ b/no_provenance.c",
                "@@ -1,1 +1,1 @@",
                "-x = 0;",
                "+x = 1;",
            ]
        )
        + "\n",
        left_entry="main",
        right_entry="main",
        alignment="legacy",
    )

    assert set(result.impact.left.impacted_blocks) == {
        "proc:main:block:entry",
        "proc:main:block:exit",
    }
    assert set(result.impact.right.impacted_blocks) == {
        "proc:main:block:entry",
        "proc:main:block:exit",
    }
    assert any("no source provenance found" in d for d in result.diagnostics)
    assert result.to_json()["summaries"]["diagnostics"] == [
        "no unchanged Boogie blocks available for summaries"
    ]


def test_summary_duplicate_signatures_pair_uniquely():
    left = """
procedure main();
implementation main()
{
  var x: int;
entry:
  assume {:sourceloc "demo.c" 2 1} true;
  x := 0;
  return;
stable_a:
  assume {:sourceloc "demo.c" 10 1} true;
  assume true;
  return;
stable_b:
  assume {:sourceloc "demo.c" 11 1} true;
  assume true;
  return;
}
"""
    right = left.replace("x := 0;", "x := 1;")
    result = build_from_bpl(
        left_bpl=left,
        right_bpl=right,
        diff_text=PATCH,
        left_entry="main",
        right_entry="main",
    )

    paired = [
        region["equivalent_to"]
        for region in result.to_json()["summaries"]["left"]
        if region["block_label"].startswith("stable_")
    ]
    assert sorted(paired) == [
        "proc:main:block:stable_a",
        "proc:main:block:stable_b",
    ]


def test_failure_cut_uses_verifier_output_when_available():
    result = build_from_bpl(
        left_bpl=LEFT_BPL,
        right_bpl=RIGHT_BPL,
        diff_text=PATCH,
        left_entry="main",
        right_entry="main",
        verifier_output="assertion failed in proc:main:block:exit",
    )

    cut = result.to_json()["failure_cut"]
    assert any(
        entry["node_id"] == "proc:main:block:exit" and entry["reason"] == "verifier-output"
        for entry in cut
    )
    assert all(entry["reason"] == "verifier-output" for entry in cut)


def test_actual_product_records_impacted_call_blocks():
    bpl = """
procedure foo();
procedure main();
implementation main()
{
entry:
  assume {:sourceloc "demo.c" 2 1} true;
  call foo();
  return;
}
"""
    result = build_from_bpl(
        left_bpl=bpl,
        right_bpl=bpl,
        diff_text="\n".join(
            [
                "--- a/demo.c",
                "+++ b/demo.c",
                "@@ -2,1 +2,1 @@",
                "-call foo();",
                "+call bar();",
            ]
        )
        + "\n",
        left_entry="main",
        right_entry="main",
        alignment="legacy",
    )

    report = result.to_json()["product"]
    assert report["actual_product_available"] is True
    assert report["actual_source"] == "diffprod-product-v2"
    assert report["delta"]["left_blocks"] == ["entry"]
    assert report["delta"]["right_blocks"] == ["entry"]
    assert "{:delta true}" in result.product.text


def test_smack_generated_bpl_builds_egraph_product(tmp_path):
    left = tmp_path / "left.c"
    right = tmp_path / "right.c"
    diff = tmp_path / "change.diff"
    left_bpl = tmp_path / "left.bpl"
    right_bpl = tmp_path / "right.bpl"
    left.write_text("int f(int x) {\n  return x + 0;\n}\n")
    right.write_text("int f(int x) {\n  return x - 0;\n}\n")
    diff.write_text(
        "\n".join(
            [
                "--- a/left.c",
                "+++ b/right.c",
                "@@ -2,1 +2,1 @@",
                "-  return x + 0;",
                "+  return x - 0;",
            ]
        )
        + "\n"
    )

    run_with_timeout(
        [smack_executable(), "-t", "--entry-points", "f", "-bpl", str(left_bpl), str(left)],
        cwd=tmp_path,
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        env=tool_path_env(),
        timeout_name="SMACK",
        default_timeout=180,
    )
    run_with_timeout(
        [smack_executable(), "-t", "--entry-points", "f", "-bpl", str(right_bpl), str(right)],
        cwd=tmp_path,
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        env=tool_path_env(),
        timeout_name="SMACK",
        default_timeout=180,
    )

    result = build_from_bpl(
        left_bpl=left_bpl.read_text(),
        right_bpl=right_bpl.read_text(),
        diff_text=diff.read_text(),
        left_entry="f",
        right_entry="f",
        alignment="legacy",
    )

    assert result.product.actual_product_available is True
    assert result.product.actual_source == "diffprod-product-v2"
    report = result.to_json()["product"]
    assert report["egraph_success"] is True
    assert any(
        outcome["success"]
        and outcome["resolution"].startswith("egraph")
        and outcome["region"]["left_blocks"] == ["$bb0.P"]
        and outcome["region"]["right_blocks"] == ["$bb0.Q"]
        and outcome["debug_steps"]
        for outcome in report["egraph_outcomes"]
    )
    assert "$bb0.P:" in result.product.text
    assert "$bb0.Q:" in result.product.text
    assert "// diffprod.trace_pair resolution=egraph" in result.product.text
    assert "// diffprod.egraph.step region=$bb0.P->$bb0.Q" in result.product.text
    assert "assert" in result.product.text
    product = tmp_path / "product.bpl"
    product.write_text(result.product.text)
    assert_boogie_verifies(product)


def test_smack_auto_alignment_reports_candidate_selection(tmp_path):
    result, product = build_smack_product(
        tmp_path,
        "auto_select",
        "int f(int x) {\n  return x + 0;\n}\n",
        "int f(int x) {\n  return x - 0;\n}\n",
        "\n".join(
            [
                "--- a/auto_select_left.c",
                "+++ b/auto_select_right.c",
                "@@ -2,1 +2,1 @@",
                "-  return x + 0;",
                "+  return x - 0;",
            ]
        )
        + "\n",
        alignment="auto",
    )

    report = result.to_json()["product"]
    labels = {candidate["label"] for candidate in report["selection"]}
    assert {"baseline", "legacy"} <= labels
    assert report["mode"] == "legacy"
    assert any(
        candidate["label"] == "legacy"
        and candidate["selected"]
        and candidate["egraph_success_count"] >= 1
        for candidate in report["selection"]
    )
    assert_boogie_verifies(product)


def test_smack_product_runs_in_interpreter_and_matches_side_returns(tmp_path):
    result, product = build_smack_product(
        tmp_path,
        "interpreter_equiv",
        "int f(int x) {\n  return x + 1;\n}\n",
        "int f(int x) {\n  return 1 + x;\n}\n",
        "\n".join(
            [
                "--- a/interpreter_equiv_left.c",
                "+++ b/interpreter_equiv_right.c",
                "@@ -2,1 +2,1 @@",
                "-  return x + 1;",
                "+  return 1 + x;",
            ]
        )
        + "\n",
        alignment="auto",
    )

    assert_product_naming_invariants(result)
    assert "$i0.P" not in result.product.text
    assert "$i0.Q" not in result.product.text
    for value in [0, 3, -5]:
        run = run_product_with_interpreter(
            result.product.text,
            tmp_path,
            f"interpreter_equiv_{value}",
            {"$i0": value},
        )
        assert run["status"] == "ok", run
        assert run["final_scalars"]["$r.P"] == value + 1
        assert run["final_scalars"]["$r.Q"] == value + 1
    assert_boogie_verifies(product)


def test_smack_product_interpreter_rejects_return_mismatch(tmp_path):
    result, product = build_smack_product(
        tmp_path,
        "interpreter_negative",
        "int f(int x) {\n  return x + 1;\n}\n",
        "int f(int x) {\n  return x + 2;\n}\n",
        "\n".join(
            [
                "--- a/interpreter_negative_left.c",
                "+++ b/interpreter_negative_right.c",
                "@@ -2,1 +2,1 @@",
                "-  return x + 1;",
                "+  return x + 2;",
            ]
        )
        + "\n",
        alignment="baseline",
    )

    run = run_product_with_interpreter(
        result.product.text,
        tmp_path,
        "interpreter_negative",
        {"$i0": 4},
    )
    assert run["status"] == "assert_violation", run
    assert run["violation_block"] == "diffprod_exit"
    assert run["final_scalars"]["$r.P"] == 5
    assert run["final_scalars"]["$r.Q"] == 6
    assert_boogie_rejects(product)


def test_smack_multistep_scalar_diff_emits_egraph_debug_trace(tmp_path):
    result, product = build_smack_product(
        tmp_path,
        "multistep",
        "\n".join(
            [
                "int f(int x) {",
                "  int a = x + 0;",
                "  int b = a * 1;",
                "  return b + 0;",
                "}",
            ]
        )
        + "\n",
        "\n".join(
            [
                "int f(int x) {",
                "  int a = x - 0;",
                "  int b = 1 * a;",
                "  return b - 0;",
                "}",
            ]
        )
        + "\n",
        "\n".join(
            [
                "--- a/multistep_left.c",
                "+++ b/multistep_right.c",
                "@@ -2,3 +2,3 @@",
                "-  int a = x + 0;",
                "-  int b = a * 1;",
                "-  return b + 0;",
                "+  int a = x - 0;",
                "+  int b = 1 * a;",
                "+  return b - 0;",
            ]
        )
        + "\n",
    )

    report = result.to_json()["product"]
    egraph_outcomes = [
        outcome
        for outcome in report["egraph_outcomes"]
        if outcome["success"] and outcome["resolution"] == "egraph"
    ]
    assert egraph_outcomes
    phases = {step["phase"] for outcome in egraph_outcomes for step in outcome["debug_steps"]}
    assert {"collect-region", "encode-egglog", "run-egglog", "apply-alignment"} <= phases
    assert "$bb0.P:" in result.product.text
    assert "$bb0.Q:" in result.product.text
    assert "// diffprod.egraph.step region=$bb0.P->$bb0.Q" in result.product.text
    assert_egraph_step_comments_match_report(result)
    assert_boogie_verifies(product)


def test_smack_no_egraph_mode_keeps_valid_product_without_egraph_success(tmp_path):
    result, product = build_smack_product(
        tmp_path,
        "no_egraph",
        "int f(int x) {\n  return x + 0;\n}\n",
        "int f(int x) {\n  return x - 0;\n}\n",
        "\n".join(
            [
                "--- a/no_egraph_left.c",
                "+++ b/no_egraph_right.c",
                "@@ -2,1 +2,1 @@",
                "-  return x + 0;",
                "+  return x - 0;",
            ]
        )
        + "\n",
        no_egraph=True,
    )

    assert_product_naming_invariants(result)
    report = result.to_json()["product"]
    assert report["mode"] == "legacy"
    assert report["egraph_success"] is False
    assert report["egraph_outcomes"] == []
    assert "// diffprod.trace_pair" not in result.product.text
    assert "// diffprod.egraph.step" not in result.product.text
    assert_boogie_verifies(product)


def test_smack_baseline_mode_has_no_alignment_comments(tmp_path):
    result, product = build_smack_product(
        tmp_path,
        "baseline_mode",
        "int f(int x) {\n  return x + 0;\n}\n",
        "int f(int x) {\n  return x - 0;\n}\n",
        "\n".join(
            [
                "--- a/baseline_mode_left.c",
                "+++ b/baseline_mode_right.c",
                "@@ -2,1 +2,1 @@",
                "-  return x + 0;",
                "+  return x - 0;",
            ]
        )
        + "\n",
        alignment="baseline",
    )

    assert_product_naming_invariants(result)
    report = result.to_json()["product"]
    assert report["mode"] == "baseline"
    assert report["lockstep_outcomes"] == []
    assert report["egraph_outcomes"] == []
    assert "// diffprod.trace_pair" not in result.product.text
    assert "// diffprod.egraph.step" not in result.product.text
    assert_boogie_verifies(product)


def test_smack_large_straightline_multiple_hunks_aligns_and_verifies(tmp_path):
    result, product = build_smack_product(
        tmp_path,
        "large_straightline",
        "\n".join(
            [
                "int f(int x, int y) {",
                "  int a = x + 0;",
                "  int b = y + 1;",
                "  int c = a + b;",
                "  int d = c * 1;",
                "  int e = d + 2;",
                "  int g = e - 0;",
                "  int h = g + (x - x);",
                "  return h + 0;",
                "}",
            ]
        )
        + "\n",
        "\n".join(
            [
                "int f(int x, int y) {",
                "  int a = x - 0;",
                "  int b = y + 1;",
                "  int c = b + a;",
                "  int d = 1 * c;",
                "  int e = d + 2;",
                "  int g = e - 0;",
                "  int h = g + (x - x);",
                "  return h - 0;",
                "}",
            ]
        )
        + "\n",
        "\n".join(
            [
                "--- a/large_straightline_left.c",
                "+++ b/large_straightline_right.c",
                "@@ -2,4 +2,4 @@",
                "-  int a = x + 0;",
                "+  int a = x - 0;",
                "   int b = y + 1;",
                "-  int c = a + b;",
                "-  int d = c * 1;",
                "+  int c = b + a;",
                "+  int d = 1 * c;",
                "@@ -9,1 +9,1 @@",
                "-  return h + 0;",
                "+  return h - 0;",
            ]
        )
        + "\n",
    )

    report = assert_product_core_invariants(result)
    assert report["egraph_success"] is True
    successes = assert_egraph_success_with_debug(report)
    assert any(len(o["debug_steps"]) >= 5 for o in successes)
    assert "// diffprod.trace_pair resolution=egraph" in result.product.text
    assert_boogie_verifies(product)


def test_smack_large_branch_multiple_diff_regions_verifies_with_diagnostics(tmp_path):
    result, product = build_smack_product(
        tmp_path,
        "large_branch",
        "\n".join(
            [
                "int f(int x, int y) {",
                "  int base = x + y;",
                "  int out = base + 0;",
                "  if (base > 0) {",
                "    int a = out + 0;",
                "    int b = a * 1;",
                "    out = b + y;",
                "  } else {",
                "    int c = out - 0;",
                "    int d = c + (y - y);",
                "    out = d - y;",
                "  }",
                "  return out + 0;",
                "}",
            ]
        )
        + "\n",
        "\n".join(
            [
                "int f(int x, int y) {",
                "  int base = x + y;",
                "  int out = base - 0;",
                "  if (base > 0) {",
                "    int a = out - 0;",
                "    int b = 1 * a;",
                "    out = b + y;",
                "  } else {",
                "    int c = out + 0;",
                "    int d = c + (y - y);",
                "    out = d - y;",
                "  }",
                "  return out - 0;",
                "}",
            ]
        )
        + "\n",
        "\n".join(
            [
                "--- a/large_branch_left.c",
                "+++ b/large_branch_right.c",
                "@@ -3,4 +3,4 @@",
                "-  int out = base + 0;",
                "+  int out = base - 0;",
                "   if (base > 0) {",
                "-    int a = out + 0;",
                "-    int b = a * 1;",
                "+    int a = out - 0;",
                "+    int b = 1 * a;",
                "@@ -9,1 +9,1 @@",
                "-    int c = out - 0;",
                "+    int c = out + 0;",
                "@@ -13,1 +13,1 @@",
                "-  return out + 0;",
                "+  return out - 0;",
            ]
        )
        + "\n",
    )

    report = assert_product_core_invariants(result)
    assert len(set(report["delta"]["left_blocks"])) >= 2
    assert any(not outcome["success"] for outcome in report["egraph_outcomes"])
    assert any(
        step.get("reason") == "region contains non-assignment statements"
        for outcome in report["egraph_outcomes"]
        for step in outcome["debug_steps"]
    )
    assert "goto $bb" in result.product.text
    assert_boogie_verifies(product)


def test_smack_large_call_multiple_hunks_verifies_and_declares_summaries(tmp_path):
    result, product = build_smack_product(
        tmp_path,
        "large_call",
        "\n".join(
            [
                "int g(int x) { return x + 2; }",
                "int h(int x) { return x * 1; }",
                "int f(int x) {",
                "  int a = x + 0;",
                "  int b = g(a) + 0;",
                "  int c = h(b) * 1;",
                "  int d = c + 3;",
                "  return d + 0;",
                "}",
            ]
        )
        + "\n",
        "\n".join(
            [
                "int g(int x) { return x + 2; }",
                "int h(int x) { return x * 1; }",
                "int f(int x) {",
                "  int a = x - 0;",
                "  int b = g(a) - 0;",
                "  int c = 1 * h(b);",
                "  int d = c + 3;",
                "  return d - 0;",
                "}",
            ]
        )
        + "\n",
        "\n".join(
            [
                "--- a/large_call_left.c",
                "+++ b/large_call_right.c",
                "@@ -4,4 +4,4 @@",
                "-  int a = x + 0;",
                "-  int b = g(a) + 0;",
                "-  int c = h(b) * 1;",
                "+  int a = x - 0;",
                "+  int b = g(a) - 0;",
                "+  int c = 1 * h(b);",
                "   int d = c + 3;",
                "@@ -8,1 +8,1 @@",
                "-  return d + 0;",
                "+  return d - 0;",
            ]
        )
        + "\n",
    )

    report = assert_product_core_invariants(result)
    assert "function $call.g" in result.product.text
    assert "function $call.h" in result.product.text
    assert any(not outcome["success"] for outcome in report["egraph_outcomes"])
    assert_boogie_verifies(product)


def test_smack_large_multi_diff_preserves_helper_and_impacts_downstream_cfg(tmp_path):
    left = (
        "\n".join(
            [
                "int g(int y) {",
                "  int base = y + 4;",
                "  if (base > 10) {",
                "    base = base - 1;",
                "  } else {",
                "    base = base + 1;",
                "  }",
                "  return base;",
                "}",
                "int f(int x, int y) {",
                "  int a = x + 0;",
                "  int stable = g(y);",
                "  int guard = a + 1;",
                "  if (guard > 3) {",
                "    a = a + 2;",
                "  } else {",
                "    a = a - 2;",
                "  }",
                "  int b = a * 1;",
                "  return b + stable;",
                "}",
            ]
        )
        + "\n"
    )
    right = (
        "\n".join(
            [
                "int g(int y) {",
                "  int base = y + 4;",
                "  if (base > 10) {",
                "    base = base - 1;",
                "  } else {",
                "    base = base + 1;",
                "  }",
                "  return base;",
                "}",
                "int f(int x, int y) {",
                "  int a = x - 0;",
                "  int stable = g(y);",
                "  int guard = a + 1;",
                "  if (guard > 3) {",
                "    a = a + 2;",
                "  } else {",
                "    a = a - 2;",
                "  }",
                "  int b = 1 * a;",
                "  return stable + b;",
                "}",
            ]
        )
        + "\n"
    )
    result, product = build_smack_product(
        tmp_path,
        "large_downstream_cfg",
        left,
        right,
        source_diff("large_downstream_cfg", left, right),
        alignment="auto",
    )

    report = assert_product_core_invariants(result)
    helper_summaries = [region for region in result.summaries.left if region.proc_id == "proc:g"]
    assert helper_summaries
    assert all(
        region.block_id not in result.impact.left.impacted_blocks for region in helper_summaries
    )
    assert_impact_has_reason(result, "left", "data-dependency")
    assert_impact_has_reason(result, "left", "control-dependency")
    assert_egraph_regions_are_delta_scoped(report)
    assert_boogie_verifies(product)


def test_smack_large_negative_multiple_hunks_is_rejected(tmp_path):
    result, product = build_smack_product(
        tmp_path,
        "large_negative",
        "\n".join(
            [
                "int f(int x, int y) {",
                "  int a = x + 0;",
                "  int b = y * 1;",
                "  int c = a + b;",
                "  int d = c + 4;",
                "  return d + 0;",
                "}",
            ]
        )
        + "\n",
        "\n".join(
            [
                "int f(int x, int y) {",
                "  int a = x - 0;",
                "  int b = 1 * y;",
                "  int c = b + a;",
                "  int d = c + 5;",
                "  return d - 0;",
                "}",
            ]
        )
        + "\n",
        "\n".join(
            [
                "--- a/large_negative_left.c",
                "+++ b/large_negative_right.c",
                "@@ -2,5 +2,5 @@",
                "-  int a = x + 0;",
                "-  int b = y * 1;",
                "-  int c = a + b;",
                "-  int d = c + 4;",
                "-  return d + 0;",
                "+  int a = x - 0;",
                "+  int b = 1 * y;",
                "+  int c = b + a;",
                "+  int d = c + 5;",
                "+  return d - 0;",
            ]
        )
        + "\n",
    )

    report = assert_product_core_invariants(result)
    assert any(
        not outcome["success"] and outcome["debug_steps"] for outcome in report["egraph_outcomes"]
    )
    assert_boogie_rejects(product)


def test_smack_realistic_checksum_patch_egraph_is_delta_scoped(tmp_path):
    result, product = build_smack_product(
        tmp_path,
        "realistic_checksum",
        "\n".join(
            [
                "int f(int a, int b, int c) {",
                "  int seed = 17;",
                "  int mix = a + b;",
                "  int fold = mix + 0;",
                "  int tail = c * 1;",
                "  int out = fold + tail;",
                "  return out + seed;",
                "}",
            ]
        )
        + "\n",
        "\n".join(
            [
                "int f(int a, int b, int c) {",
                "  int seed = 17;",
                "  int mix = b + a;",
                "  int fold = mix - 0;",
                "  int tail = 1 * c;",
                "  int out = tail + fold;",
                "  return seed + out;",
                "}",
            ]
        )
        + "\n",
        "\n".join(
            [
                "--- a/realistic_checksum_left.c",
                "+++ b/realistic_checksum_right.c",
                "@@ -3,5 +3,5 @@",
                "-  int mix = a + b;",
                "-  int fold = mix + 0;",
                "-  int tail = c * 1;",
                "-  int out = fold + tail;",
                "-  return out + seed;",
                "+  int mix = b + a;",
                "+  int fold = mix - 0;",
                "+  int tail = 1 * c;",
                "+  int out = tail + fold;",
                "+  return seed + out;",
            ]
        )
        + "\n",
    )

    report = assert_product_core_invariants(result)
    assert_egraph_regions_are_delta_scoped(report)
    assert_egraph_success_with_debug(report)
    assert_impact_has_reason(result, "left", "source-diff")
    assert "// diffprod.trace_pair resolution=egraph" in result.product.text
    assert_egraph_step_comments_match_report(result)
    assert_boogie_verifies(product)


def test_smack_realistic_parser_state_patch_closes_data_dependencies(tmp_path):
    result, product = build_smack_product(
        tmp_path,
        "realistic_parser_state",
        "\n".join(
            [
                "int f(int x, int y) {",
                "  int parsed = x + 0;",
                "  int folded = parsed + y;",
                "  int stable = y * 2;",
                "  return folded + stable;",
                "}",
            ]
        )
        + "\n",
        "\n".join(
            [
                "int f(int x, int y) {",
                "  int parsed = x - 0;",
                "  int folded = parsed + y;",
                "  int stable = y * 2;",
                "  return folded + stable;",
                "}",
            ]
        )
        + "\n",
        "\n".join(
            [
                "--- a/realistic_parser_state_left.c",
                "+++ b/realistic_parser_state_right.c",
                "@@ -2,1 +2,1 @@",
                "-  int parsed = x + 0;",
                "+  int parsed = x - 0;",
            ]
        )
        + "\n",
    )

    report = assert_product_core_invariants(result)
    assert_egraph_regions_are_delta_scoped(report)
    assert_egraph_success_with_debug(report)
    assert_impact_has_reason(result, "left", "source-diff")
    assert result.impact.left.variables
    assert_boogie_verifies(product)


def test_smack_realistic_branch_patch_uses_cfg_closure_and_fallback(tmp_path):
    result, product = build_smack_product(
        tmp_path,
        "realistic_branch",
        "\n".join(
            [
                "int f(int x, int y) {",
                "  int limit = y + 10;",
                "  int out = x + 0;",
                "  if (out > limit) {",
                "    out = out - limit;",
                "  } else {",
                "    out = out + y;",
                "  }",
                "  return out + 0;",
                "}",
            ]
        )
        + "\n",
        "\n".join(
            [
                "int f(int x, int y) {",
                "  int limit = y + 10;",
                "  int out = x - 0;",
                "  if (out > limit) {",
                "    out = out - limit;",
                "  } else {",
                "    out = y + out;",
                "  }",
                "  return out - 0;",
                "}",
            ]
        )
        + "\n",
        "\n".join(
            [
                "--- a/realistic_branch_left.c",
                "+++ b/realistic_branch_right.c",
                "@@ -3,1 +3,1 @@",
                "-  int out = x + 0;",
                "+  int out = x - 0;",
                "@@ -7,1 +7,1 @@",
                "-    out = out + y;",
                "+    out = y + out;",
                "@@ -9,1 +9,1 @@",
                "-  return out + 0;",
                "+  return out - 0;",
            ]
        )
        + "\n",
    )

    report = assert_product_core_invariants(result)
    assert_egraph_regions_are_delta_scoped(report)
    assert report["egraph_success"] is False
    assert_egraph_reports_non_assignment_region(report)
    assert_impact_has_reason(result, "left", "cfg-closure")
    assert "goto $bb" in result.product.text
    assert_boogie_verifies(product)


def test_smack_realistic_packet_memory_patch_verifies_with_heap_product(tmp_path):
    result, product = build_smack_product(
        tmp_path,
        "realistic_packet_memory",
        "\n".join(
            [
                "int f(int *buf, int n) {",
                "  int header = buf[0] + 0;",
                "  int folded = header + n;",
                "  buf[1] = folded * 1;",
                "  int check = buf[1] + header;",
                "  return check + 0;",
                "}",
            ]
        )
        + "\n",
        "\n".join(
            [
                "int f(int *buf, int n) {",
                "  int header = buf[0] - 0;",
                "  int folded = n + header;",
                "  buf[1] = 1 * folded;",
                "  int check = header + buf[1];",
                "  return check - 0;",
                "}",
            ]
        )
        + "\n",
        "\n".join(
            [
                "--- a/realistic_packet_memory_left.c",
                "+++ b/realistic_packet_memory_right.c",
                "@@ -2,5 +2,5 @@",
                "-  int header = buf[0] + 0;",
                "-  int folded = header + n;",
                "-  buf[1] = folded * 1;",
                "-  int check = buf[1] + header;",
                "-  return check + 0;",
                "+  int header = buf[0] - 0;",
                "+  int folded = n + header;",
                "+  buf[1] = 1 * folded;",
                "+  int check = header + buf[1];",
                "+  return check - 0;",
            ]
        )
        + "\n",
    )

    report = assert_product_core_invariants(result)
    assert_egraph_regions_are_delta_scoped(report)
    assert_egraph_reports_non_assignment_region(report)
    assert "$M.0$in: [int]int" in result.product.text
    assert "$M.1$out.P: [int]int" in result.product.text
    assert "assert ($M.1$out.P == $M.1$out.Q);" in result.product.text
    assert_boogie_verifies(product)


def test_smack_realistic_negative_patch_is_rejected_and_scoped(tmp_path):
    result, product = build_smack_product(
        tmp_path,
        "realistic_negative",
        "\n".join(
            [
                "int f(int x, int y) {",
                "  int seed = 7;",
                "  int mix = x + y;",
                "  int out = mix + seed;",
                "  return out + 0;",
                "}",
            ]
        )
        + "\n",
        "\n".join(
            [
                "int f(int x, int y) {",
                "  int seed = 7;",
                "  int mix = y + x;",
                "  int out = mix + seed + 1;",
                "  return out - 0;",
                "}",
            ]
        )
        + "\n",
        "\n".join(
            [
                "--- a/realistic_negative_left.c",
                "+++ b/realistic_negative_right.c",
                "@@ -3,3 +3,3 @@",
                "-  int mix = x + y;",
                "-  int out = mix + seed;",
                "-  return out + 0;",
                "+  int mix = y + x;",
                "+  int out = mix + seed + 1;",
                "+  return out - 0;",
            ]
        )
        + "\n",
    )

    report = assert_product_core_invariants(result)
    assert_egraph_regions_are_delta_scoped(report)
    assert report["egraph_success"] is False
    assert any(
        step["phase"] == "run-egglog" and not step["success"]
        for outcome in report["egraph_outcomes"]
        for step in outcome["debug_steps"]
    )
    assert_boogie_rejects(product)


def test_smack_branch_product_preserves_cfg_and_verifies(tmp_path):
    result, product = build_smack_product(
        tmp_path,
        "branch",
        "int f(int x) {\n  if (x > 0) return x + 1;\n  return x + 0;\n}\n",
        "int f(int x) {\n  if (x > 0) return x + 1;\n  return x - 0;\n}\n",
        "\n".join(
            [
                "--- a/branch_left.c",
                "+++ b/branch_right.c",
                "@@ -3,1 +3,1 @@",
                "-  return x + 0;",
                "+  return x - 0;",
            ]
        )
        + "\n",
    )

    assert result.product.actual_product_available is True
    assert "goto $bb1.P, $bb2.P;" in result.product.text
    assert "(if ($i0 > 0) then 1 else 0)" in result.product.text
    assert_boogie_verifies(product)


def test_smack_call_product_uses_deterministic_summary_and_verifies(tmp_path):
    result, product = build_smack_product(
        tmp_path,
        "call",
        "int g(int x) { return x + 1; }\nint f(int x) { return g(x) + 0; }\n",
        "int g(int x) { return x + 1; }\nint f(int x) { return g(x) - 0; }\n",
        "\n".join(
            [
                "--- a/call_left.c",
                "+++ b/call_right.c",
                "@@ -2,1 +2,1 @@",
                "-int f(int x) { return g(x) + 0; }",
                "+int f(int x) { return g(x) - 0; }",
            ]
        )
        + "\n",
    )

    assert result.product.actual_product_available is True
    assert "function $call.g(a0: int) returns (int);" in result.product.text
    assert "$i1.P := $call.g($i0);" in result.product.text
    report = result.to_json()["product"]
    assert any(
        not outcome["success"] and outcome["debug_steps"] for outcome in report["egraph_outcomes"]
    )
    assert_boogie_verifies(product)


def test_smack_memory_product_tracks_heap_map_and_verifies(tmp_path):
    result, product = build_smack_product(
        tmp_path,
        "memory",
        "int f(int *p) {\n  p[0] = p[0] + 1;\n  return p[0] + 0;\n}\n",
        "int f(int *p) {\n  p[0] = p[0] + 1;\n  return p[0] - 0;\n}\n",
        "\n".join(
            [
                "--- a/memory_left.c",
                "+++ b/memory_right.c",
                "@@ -3,1 +3,1 @@",
                "-  return p[0] + 0;",
                "+  return p[0] - 0;",
            ]
        )
        + "\n",
    )

    assert result.product.actual_product_available is True
    assert "$M.0$in: [int]int" in result.product.text
    assert "$M.0$out.P: [int]int" in result.product.text
    assert "$M.0.P[$p4.P] := $i3.P;" in result.product.text
    assert "assert ($M.0$out.P == $M.0$out.Q);" in result.product.text
    assert_boogie_verifies(product)


def test_smack_loop_product_preserves_backedge_and_verifies_with_unroll(tmp_path):
    result, product = build_smack_product(
        tmp_path,
        "loop",
        "\n".join(
            [
                "int f(int n) {",
                "  int s = 0;",
                "  for (int i = 0; i < n; i++) s += i;",
                "  return s + 0;",
                "}",
            ]
        )
        + "\n",
        "\n".join(
            [
                "int f(int n) {",
                "  int s = 0;",
                "  for (int i = 0; i < n; i++) s += i;",
                "  return s - 0;",
                "}",
            ]
        )
        + "\n",
        "\n".join(
            [
                "--- a/loop_left.c",
                "+++ b/loop_right.c",
                "@@ -4,1 +4,1 @@",
                "-  return s + 0;",
                "+  return s - 0;",
            ]
        )
        + "\n",
    )

    assert result.product.actual_product_available is True
    assert "goto $bb1.P;" in result.product.text
    assert "goto $bb1.Q;" in result.product.text
    assert "(if ($i2.P < $i0) then 1 else 0)" in result.product.text
    assert_boogie_verifies(product, "/loopUnroll:3")


SLOW_STRESS_CASES = [
    pytest.param(
        "stress_straightline_30_statements",
        "\n".join(
            [
                "int f(int x, int y) {",
                "  int a0 = x + 0;",
                "  int a1 = a0 + y;",
                "  int a2 = a1 * 1;",
                "  int a3 = a2 + 3;",
                "  int a4 = a3 - 0;",
                "  int a5 = a4 + (x - x);",
                "  int a6 = a5 + 6;",
                "  int a7 = a6 * 1;",
                "  int a8 = a7 + y;",
                "  int a9 = a8 - 0;",
                "  int a10 = a9 + 10;",
                "  int a11 = a10 * 1;",
                "  int a12 = a11 + (y - y);",
                "  int a13 = a12 + 13;",
                "  int a14 = a13 - 0;",
                "  int a15 = a14 + 15;",
                "  int a16 = a15 * 1;",
                "  int a17 = a16 + (x - x);",
                "  int a18 = a17 + 18;",
                "  int a19 = a18 - 0;",
                "  return a19 + 0;",
                "}",
            ]
        )
        + "\n",
        "\n".join(
            [
                "int f(int x, int y) {",
                "  int a0 = x - 0;",
                "  int a1 = y + a0;",
                "  int a2 = 1 * a1;",
                "  int a3 = a2 + 3;",
                "  int a4 = a3 + 0;",
                "  int a5 = a4 + (x - x);",
                "  int a6 = a5 + 6;",
                "  int a7 = 1 * a6;",
                "  int a8 = y + a7;",
                "  int a9 = a8 - 0;",
                "  int a10 = a9 + 10;",
                "  int a11 = 1 * a10;",
                "  int a12 = a11 + (y - y);",
                "  int a13 = a12 + 13;",
                "  int a14 = a13 + 0;",
                "  int a15 = a14 + 15;",
                "  int a16 = 1 * a15;",
                "  int a17 = a16 + (x - x);",
                "  int a18 = a17 + 18;",
                "  int a19 = a18 - 0;",
                "  return a19 - 0;",
                "}",
            ]
        )
        + "\n",
        "\n".join(
            [
                "--- a/stress_straightline_30_statements_left.c",
                "+++ b/stress_straightline_30_statements_right.c",
                "@@ -2,4 +2,4 @@",
                "-  int a0 = x + 0;",
                "-  int a1 = a0 + y;",
                "-  int a2 = a1 * 1;",
                "+  int a0 = x - 0;",
                "+  int a1 = y + a0;",
                "+  int a2 = 1 * a1;",
                "   int a3 = a2 + 3;",
                "@@ -9,5 +9,5 @@",
                "-  int a7 = a6 * 1;",
                "-  int a8 = a7 + y;",
                "+  int a7 = 1 * a6;",
                "+  int a8 = y + a7;",
                "   int a9 = a8 - 0;",
                "   int a10 = a9 + 10;",
                "-  int a11 = a10 * 1;",
                "+  int a11 = 1 * a10;",
                "@@ -16,7 +16,7 @@",
                "-  int a14 = a13 - 0;",
                "+  int a14 = a13 + 0;",
                "   int a15 = a14 + 15;",
                "-  int a16 = a15 * 1;",
                "+  int a16 = 1 * a15;",
                "   int a17 = a16 + (x - x);",
                "   int a18 = a17 + 18;",
                "   int a19 = a18 - 0;",
                "-  return a19 + 0;",
                "+  return a19 - 0;",
            ]
        )
        + "\n",
        True,
        (),
        id="straightline",
    ),
    pytest.param(
        "stress_loop_pre_post",
        "\n".join(
            [
                "int f(int n) {",
                "  int s = 0;",
                "  int seed = n + 0;",
                "  for (int i = 0; i < n; i++) {",
                "    s = s + i;",
                "  }",
                "  int tail = s + seed;",
                "  return tail + 0;",
                "}",
            ]
        )
        + "\n",
        "\n".join(
            [
                "int f(int n) {",
                "  int s = 0;",
                "  int seed = n - 0;",
                "  for (int i = 0; i < n; i++) {",
                "    s = s + i + 0;",
                "  }",
                "  int tail = seed + s;",
                "  return tail - 0;",
                "}",
            ]
        )
        + "\n",
        "\n".join(
            [
                "--- a/stress_loop_pre_post_left.c",
                "+++ b/stress_loop_pre_post_right.c",
                "@@ -3,1 +3,1 @@",
                "-  int seed = n + 0;",
                "+  int seed = n - 0;",
                "@@ -5,1 +5,1 @@",
                "-    s = s + i;",
                "+    s = s + i + 0;",
                "@@ -7,2 +7,2 @@",
                "-  int tail = s + seed;",
                "-  return tail + 0;",
                "+  int tail = seed + s;",
                "+  return tail - 0;",
            ]
        )
        + "\n",
        True,
        ("/loopUnroll:4",),
        id="loop",
    ),
    pytest.param(
        "stress_memory_multi_store",
        "\n".join(
            [
                "int f(int *p, int x) {",
                "  p[0] = x + 0;",
                "  p[1] = p[0] + 1;",
                "  p[2] = p[1] * 1;",
                "  return p[2] + 0;",
                "}",
            ]
        )
        + "\n",
        "\n".join(
            [
                "int f(int *p, int x) {",
                "  p[0] = x - 0;",
                "  p[1] = p[0] + 1;",
                "  p[2] = 1 * p[1];",
                "  return p[2] - 0;",
                "}",
            ]
        )
        + "\n",
        "\n".join(
            [
                "--- a/stress_memory_multi_store_left.c",
                "+++ b/stress_memory_multi_store_right.c",
                "@@ -2,4 +2,4 @@",
                "-  p[0] = x + 0;",
                "+  p[0] = x - 0;",
                "   p[1] = p[0] + 1;",
                "-  p[2] = p[1] * 1;",
                "-  return p[2] + 0;",
                "+  p[2] = 1 * p[1];",
                "+  return p[2] - 0;",
            ]
        )
        + "\n",
        True,
        (),
        id="memory",
    ),
    pytest.param(
        "stress_mixed_call_branch",
        "\n".join(
            [
                "int g(int x) { return x + 1; }",
                "int h(int x) { return x + 2; }",
                "int f(int x, int y) {",
                "  int a = g(x) + 0;",
                "  int out = a + y;",
                "  if (out > 10) {",
                "    out = h(out) * 1;",
                "  } else {",
                "    out = out + 0;",
                "  }",
                "  return out + 0;",
                "}",
            ]
        )
        + "\n",
        "\n".join(
            [
                "int g(int x) { return x + 1; }",
                "int h(int x) { return x + 2; }",
                "int f(int x, int y) {",
                "  int a = g(x) - 0;",
                "  int out = y + a;",
                "  if (out > 10) {",
                "    out = 1 * h(out);",
                "  } else {",
                "    out = out - 0;",
                "  }",
                "  return out - 0;",
                "}",
            ]
        )
        + "\n",
        "\n".join(
            [
                "--- a/stress_mixed_call_branch_left.c",
                "+++ b/stress_mixed_call_branch_right.c",
                "@@ -4,8 +4,8 @@",
                "-  int a = g(x) + 0;",
                "-  int out = a + y;",
                "+  int a = g(x) - 0;",
                "+  int out = y + a;",
                "   if (out > 10) {",
                "-    out = h(out) * 1;",
                "+    out = 1 * h(out);",
                "   } else {",
                "-    out = out + 0;",
                "+    out = out - 0;",
                "   }",
                "-  return out + 0;",
                "+  return out - 0;",
            ]
        )
        + "\n",
        True,
        (),
        id="mixed-call-branch",
    ),
    pytest.param(
        "stress_negative_branch",
        "\n".join(
            [
                "int f(int x, int y) {",
                "  int out = x + y;",
                "  if (out > 0) {",
                "    out = out + 3;",
                "  } else {",
                "    out = out - 3;",
                "  }",
                "  return out + 0;",
                "}",
            ]
        )
        + "\n",
        "\n".join(
            [
                "int f(int x, int y) {",
                "  int out = y + x;",
                "  if (out > 0) {",
                "    out = out + 4;",
                "  } else {",
                "    out = out - 3;",
                "  }",
                "  return out - 0;",
                "}",
            ]
        )
        + "\n",
        "\n".join(
            [
                "--- a/stress_negative_branch_left.c",
                "+++ b/stress_negative_branch_right.c",
                "@@ -2,7 +2,7 @@",
                "-  int out = x + y;",
                "+  int out = y + x;",
                "   if (out > 0) {",
                "-    out = out + 3;",
                "+    out = out + 4;",
                "   } else {",
                "     out = out - 3;",
                "   }",
                "-  return out + 0;",
                "+  return out - 0;",
            ]
        )
        + "\n",
        False,
        (),
        id="negative-branch",
    ),
]


@pytest.mark.slow
@pytest.mark.parametrize(
    "name,left_source,right_source,diff_text,should_verify,boogie_args",
    SLOW_STRESS_CASES,
)
def test_smack_slow_stress_multi_diff_matrix(
    tmp_path,
    name,
    left_source,
    right_source,
    diff_text,
    should_verify,
    boogie_args,
):
    result, product = build_smack_product(tmp_path, name, left_source, right_source, diff_text)

    report = assert_product_core_invariants(result)
    assert len(report["delta"]["left_blocks"]) >= 1
    assert len(report["delta"]["right_blocks"]) >= 1
    if should_verify:
        assert_boogie_verifies(product, *boogie_args)
    else:
        assert_boogie_rejects(product, *boogie_args)


def _smack_blas_params():
    return (
        ["alpha", "beta"]
        + [f"a{row}{col}" for row in range(2) for col in range(2)]
        + [f"b{row}{col}" for row in range(2) for col in range(2)]
        + [f"c{row}{col}" for row in range(2) for col in range(2)]
    )


def _smack_blas_source(version):
    params = ", ".join(f"int {name}" for name in _smack_blas_params())
    lines = [f"int f({params}) {{"]
    if version == "v0":
        lines.extend(
            [
                "  int p00 = (a00 * b00) + (a01 * b10);",
                "  int p01 = (a00 * b01) + (a01 * b11);",
                "  int p10 = (a10 * b00) + (a11 * b10);",
                "  int p11 = (a10 * b01) + (a11 * b11);",
                "  int o00 = (alpha * p00) + (beta * c00);",
                "  int o01 = (alpha * p01) + (beta * c01);",
                "  int o10 = (alpha * p10) + (beta * c10);",
                "  int o11 = (alpha * p11) + (beta * c11);",
                "  return ((o00 + o01) + (o10 + o11));",
            ]
        )
    elif version == "v1":
        lines.extend(
            [
                "  int p00 = ((a00 * b00) + (a01 * b10)) + 0;",
                "  int p01 = ((a00 * b01) + (a01 * b11)) - 0;",
                "  int p10 = ((a10 * b00) + (a11 * b10)) + 0;",
                "  int p11 = ((a10 * b01) + (a11 * b11)) - 0;",
                "  int o00 = (alpha * p00) + ((beta * c00) * 1);",
                "  int o01 = (alpha * p01) + ((beta * c01) * 1);",
                "  int o10 = (alpha * p10) + ((beta * c10) * 1);",
                "  int o11 = (alpha * p11) + ((beta * c11) * 1);",
                "  return (((o00 + o01) + (o10 + o11)) + 0);",
            ]
        )
    elif version == "v2":
        lines.extend(
            [
                "  int m000 = a00 * b00;",
                "  int m001 = a01 * b10;",
                "  int p00 = m000 + m001;",
                "  int m010 = a00 * b01;",
                "  int m011 = a01 * b11;",
                "  int p01 = m010 + m011;",
                "  int m100 = a10 * b00;",
                "  int m101 = a11 * b10;",
                "  int p10 = m100 + m101;",
                "  int m110 = a10 * b01;",
                "  int m111 = a11 * b11;",
                "  int p11 = m110 + m111;",
                "  int row0 = ((alpha * p00) + (beta * c00)) + ((alpha * p01) + (beta * c01));",
                "  int row1 = ((alpha * p10) + (beta * c10)) + ((alpha * p11) + (beta * c11));",
                "  return row0 + row1;",
            ]
        )
    elif version == "v3_bug":
        lines.extend(
            [
                "  int m000 = a00 * b00;",
                "  int m001 = a01 * b10;",
                "  int p00 = m000 + m001;",
                "  int m010 = a00 * b01;",
                "  int m011 = a01 * b11;",
                "  int p01 = m010 + m011;",
                "  int m100 = a10 * b00;",
                "  int m101 = a11 * b10;",
                "  int p10 = m100 + m101;",
                "  int m110 = a10 * b01;",
                "  int m111 = a11 * b11;",
                "  int p11 = m110 + m111;",
                "  int row0 = ((alpha * p00) + (beta * c00)) + ((alpha * p01) + (beta * c01));",
                "  int row1 = ((alpha * p10) + (beta * c10)) + ((alpha * p11) + (beta * c10));",
                "  return row0 + row1;",
            ]
        )
    else:
        raise AssertionError(version)
    lines.append("}")
    return "\n".join(lines) + "\n"


def _smack_blas_inputs():
    values = {
        "alpha": 2,
        "beta": 3,
        "a00": 1,
        "a01": 2,
        "a10": 3,
        "a11": 4,
        "b00": 5,
        "b01": 6,
        "b10": 7,
        "b11": 8,
        "c00": 9,
        "c01": 10,
        "c10": 11,
        "c11": -2,
    }
    return {f"$i{idx}": values[name] for idx, name in enumerate(_smack_blas_params())}


@pytest.mark.slow
def test_smack_slow_blas_successive_version_products_run_in_interpreter(tmp_path):
    versions = [
        _smack_blas_source("v0"),
        _smack_blas_source("v1"),
        _smack_blas_source("v2"),
        _smack_blas_source("v3_bug"),
    ]
    expected_ok = [True, True, False]

    for index, (left, right, should_verify_concretely) in enumerate(
        zip(versions, versions[1:], expected_ok)
    ):
        name = f"smack_blas_v{index}_to_v{index + 1}"
        result, _product = build_smack_product(
            tmp_path,
            name,
            left,
            right,
            source_diff(name, left, right),
            alignment="auto",
        )

        report = result.to_json()["product"]
        assert_product_naming_invariants(result)
        assert report["delta"]["left_blocks"]
        assert report["delta"]["right_blocks"]
        assert sum(1 for candidate in report["selection"] if candidate["selected"]) == 1

        run = run_product_with_interpreter(
            result.product.text,
            tmp_path,
            name,
            _smack_blas_inputs(),
        )
        if should_verify_concretely:
            assert run["status"] == "ok", run
            assert run["final_scalars"]["$r.P"] == run["final_scalars"]["$r.Q"]
        else:
            assert run["status"] == "assert_violation", run
            assert run["violation_block"] == "diffprod_exit"

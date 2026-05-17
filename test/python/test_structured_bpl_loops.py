import importlib.util
import json
import re
import subprocess
import sys

import pytest
from smack_test_paths import (
    BOOGIE_PARSER_ROOT,
    REPO_ROOT,
    clang_path,
    llvm_link_path,
    run_with_timeout,
    tool_path,
)

sys.path.insert(0, str(BOOGIE_PARSER_ROOT))
from interpreter.parser.boogie_parser import parse_boogie


def load_svf_adapter_module():
    module_path = REPO_ROOT / "tools" / "svf_memory_partition_adapter.py"
    spec = importlib.util.spec_from_file_location("svf_memory_partition_adapter", module_path)
    assert spec is not None
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def compile_c_to_linked_bc(tmp_path, name, source):
    src = tmp_path / f"{name}.c"
    bc = tmp_path / f"{name}.bc"
    runtime_bc = tmp_path / f"{name}-smack-runtime.bc"
    linked = tmp_path / f"{name}-linked.bc"
    src.write_text(source)
    run_with_timeout(
        [
            clang_path(),
            "-O0",
            "-g",
            "-emit-llvm",
            "-c",
            str(src),
            "-o",
            str(bc),
        ],
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        timeout_name="LLVM",
        default_timeout=60,
    )
    run_with_timeout(
        [
            clang_path(),
            "-O0",
            "-g",
            "-emit-llvm",
            "-c",
            f"-I{REPO_ROOT / 'share' / 'smack' / 'include'}",
            str(REPO_ROOT / "share" / "smack" / "lib" / "smack.c"),
            "-o",
            str(runtime_bc),
        ],
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        timeout_name="LLVM",
        default_timeout=60,
    )
    run_with_timeout(
        [llvm_link_path(), str(bc), str(runtime_bc), "-o", str(linked)],
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        timeout_name="LLVM",
        default_timeout=60,
    )
    return linked


def default_memory_partitioner_args(extra_args):
    if any(
        "smack-memory-partitioner" in arg or "no-memory-splitting" in arg
        for arg in extra_args
    ):
        return []
    return ["-smack-memory-partitioner=sea-dsa"]


def has_memory_partition_args(extra_args):
    return any(
        "smack-memory-partitioner" in arg
        or "smack-memory-partition-oracle" in arg
        or "no-memory-splitting" in arg
        for arg in extra_args
    )


def emit_bpl(tmp_path, name, source, *extra_args):
    linked = compile_c_to_linked_bc(tmp_path, name, source)
    bpl = tmp_path / f"{name}.bpl"
    completed = run_with_timeout(
        [
            tool_path("llvm2bpl"),
            *default_memory_partitioner_args(extra_args),
            *extra_args,
            f"--bpl={bpl}",
            "--entry-points=f",
            str(linked),
        ],
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        check=False,
        timeout_name="SMACK_TOOL",
        default_timeout=120,
    )
    assert completed.returncode == 0, completed.stdout
    return bpl.read_text(), completed.stdout


def emit_paired_product_bpl(tmp_path, name, source, *extra_args):
    left = compile_c_to_linked_bc(tmp_path, f"{name}_left", source)
    right = compile_c_to_linked_bc(tmp_path, f"{name}_right", source)
    left_bpl = tmp_path / f"{name}_left.bpl"
    right_bpl = tmp_path / f"{name}_right.bpl"
    match_json = tmp_path / f"{name}_match.json"
    memory_args = []
    if not has_memory_partition_args(extra_args):
        oracle = write_bundled_svf_oracle(tmp_path, name, left, right)
        memory_args = [f"-smack-memory-partition-oracle={oracle}"]
    completed = run_with_timeout(
        [
            tool_path("llvm-diffmatch2bpl"),
            *memory_args,
            "--left-bc",
            str(left),
            "--right-bc",
            str(right),
            "--left-entry",
            "f",
            "--right-entry",
            "f",
            "--left-bpl",
            str(left_bpl),
            "--right-bpl",
            str(right_bpl),
            "--match-json",
            str(match_json),
            "-entry-points",
            "f",
            *extra_args,
        ],
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        check=False,
        timeout_name="SMACK_TOOL",
        default_timeout=120,
    )
    assert completed.returncode == 0, completed.stdout
    return left_bpl.read_text(), right_bpl.read_text(), completed.stdout


def run_llvm2bpl_on_linked(tmp_path, name, linked, entry_point, *extra_args):
    bpl = tmp_path / f"{name}.bpl"
    return run_with_timeout(
        [
            tool_path("llvm2bpl"),
            *default_memory_partitioner_args(extra_args),
            *extra_args,
            f"--bpl={bpl}",
            f"--entry-points={entry_point}",
            str(linked),
        ],
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        check=False,
        timeout_name="SMACK_TOOL",
        default_timeout=120,
    )


def run_llvm2bpl(tmp_path, name, source, *extra_args):
    linked = compile_c_to_linked_bc(tmp_path, name, source)
    return run_llvm2bpl_on_linked(tmp_path, name, linked, "f", *extra_args)


def run_raw_llvm2bpl_on_linked(tmp_path, name, linked, entry_point, *extra_args):
    bpl = tmp_path / f"{name}.bpl"
    return run_with_timeout(
        [
            tool_path("llvm2bpl"),
            *extra_args,
            f"--bpl={bpl}",
            f"--entry-points={entry_point}",
            str(linked),
        ],
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        check=False,
        timeout_name="SMACK_TOOL",
        default_timeout=120,
    )


def fake_svf_dump_for_function_accesses(adapter, ll_text, function_name, region="MR_8"):
    chunks = [f"==========FUNCTION: {function_name}=========="]
    for key in adapter.iter_module_access_keys(ll_text):
        function, instruction = key.split("\t", 1)
        if function != function_name:
            continue
        if adapter.is_load_instruction(instruction):
            chunks.extend(
                [
                    f"LDMU({region}V_0) \tpts{{1 }}",
                    "LoadStmt: [Var2 <-- Var1]\t",
                    f"   {instruction}",
                ]
            )
        elif adapter.is_store_instruction(instruction):
            chunks.extend(
                [
                    "StoreStmt: [Var1 <-- Var2]\t",
                    f"   {instruction}",
                    f"8V_1 = STCHI({region}V_0) \tpts{{1 }}",
                ]
            )
    return "\n".join(chunks) + "\n"


def fake_svf_dump_for_unique_accesses(adapter, ll_text, function_name):
    chunks = [f"==========FUNCTION: {function_name}=========="]
    region_id = 8
    for key in adapter.iter_module_access_keys(ll_text):
        function, instruction = key.split("\t", 1)
        if function != function_name:
            continue
        region = f"MR_{region_id}"
        if adapter.is_load_instruction(instruction):
            chunks.extend(
                [
                    f"LDMU({region}V_0) \tpts{{{region_id} }}",
                    "LoadStmt: [Var2 <-- Var1]\t",
                    f"   {instruction}",
                ]
            )
        elif adapter.is_store_instruction(instruction):
            chunks.extend(
                [
                    "StoreStmt: [Var1 <-- Var2]\t",
                    f"   {instruction}",
                    f"{region_id}V_1 = STCHI({region}V_0) \tpts{{{region_id} }}",
                ]
            )
        region_id += 1
    return "\n".join(chunks) + "\n"


def fake_svf_dump_for_unique_module_accesses(adapter, ll_text):
    chunks = []
    current_function = None
    region_id = 8
    for key in adapter.iter_module_access_keys(ll_text):
        function, instruction = key.split("\t", 1)
        if function != current_function:
            chunks.append(f"==========FUNCTION: {function}==========")
            current_function = function
        region = f"MR_{region_id}"
        if adapter.is_load_instruction(instruction):
            chunks.extend(
                [
                    f"LDMU({region}V_0) \tpts{{{region_id} }}",
                    "LoadStmt: [Var2 <-- Var1]\t",
                    f"   {instruction}",
                ]
            )
        elif adapter.is_store_instruction(instruction):
            chunks.extend(
                [
                    "StoreStmt: [Var1 <-- Var2]\t",
                    f"   {instruction}",
                    f"{region_id}V_1 = STCHI({region}V_0) \tpts{{{region_id} }}",
                ]
            )
        region_id += 1
    return "\n".join(chunks) + "\n"


def build_empty_svf_oracle_for_linked(tmp_path, name, linked, *, unique_accesses=False):
    adapter = load_svf_adapter_module()
    pre_ll = tmp_path / f"{name}.pre.ll"
    completed = run_raw_llvm2bpl_on_linked(
        tmp_path,
        f"{name}_pre",
        linked,
        "f",
        "-smack-memory-partitioner=sea-dsa",
        f"--ll={pre_ll}",
    )
    assert completed.returncode == 0, completed.stdout
    ll_text = pre_ll.read_text()
    svf_output = (
        fake_svf_dump_for_unique_accesses(adapter, ll_text, "f")
        if unique_accesses
        else ""
    )
    return adapter.build_oracle(
        ll_text=ll_text,
        svf_output=svf_output,
        loop_diagnostics=True,
    )


def write_bundled_svf_oracle(tmp_path, name, left, right, *, unique_accesses=False):
    left_oracle = build_empty_svf_oracle_for_linked(
        tmp_path, f"{name}_left", left, unique_accesses=unique_accesses
    )
    right_oracle = build_empty_svf_oracle_for_linked(
        tmp_path, f"{name}_right", right, unique_accesses=unique_accesses
    )
    modules = {
        left_oracle["module_fingerprint"]: left_oracle,
        right_oracle["module_fingerprint"]: right_oracle,
    }
    bundle = {
        "schema_version": 3,
        "producer": "svf-memory-partition-bundle",
        "analysis": "andersen",
        "memory_partition": "intra-disjoint",
        "modules": modules,
        "stats": {"module_count": len(modules)},
    }
    bundle_path = tmp_path / f"{name}.svf-bundle.json"
    bundle_path.write_text(json.dumps(bundle, indent=2, sort_keys=True) + "\n")
    return bundle_path


def assert_structured_boogie(text):
    assert "while (true)" in text
    assert "break;" in text
    assert "assume {:loop_header" in text
    parse_boogie(text)


def test_structured_bpl_loops_are_opt_in(tmp_path):
    source = """
int f(int n) {
  int i = 0;
  int s = 0;
  while (i < n) {
    s += i;
    i++;
  }
  return s;
}
"""
    flat, _ = emit_bpl(tmp_path, "flat", source)
    paired_flat, _, _ = emit_paired_product_bpl(tmp_path, "paired_flat", source)
    structured, _, log = emit_paired_product_bpl(
        tmp_path, "structured", source, "--structured-bpl-loops-strict"
    )
    rejected = run_llvm2bpl(tmp_path, "single_rejected", source, "--structured-bpl-loops")

    assert "while (true)" not in flat
    assert "while (true)" not in paired_flat
    assert rejected.returncode != 0
    assert "structured-bpl-loops" in rejected.stdout
    assert "SMACK structured Boogie loop" in log
    assert_structured_boogie(structured)


def test_structured_bpl_loop_driver_flag_requires_product_mode(tmp_path):
    source = tmp_path / "single.c"
    source.write_text("int f(int x) { return x; }\n")

    completed = run_with_timeout(
        [
            sys.executable,
            "-c",
            (
                "import sys; "
                f"sys.path.insert(0, {str(REPO_ROOT / 'share')!r}); "
                "from smack import top; "
                "sys.argv = ['smack', "
                "'--diff-product-structured-bpl-loops', "
                "sys.argv[1]]; "
                "top.arguments()"
            ),
            str(source),
        ],
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        check=False,
        timeout_name="PYTHON",
        default_timeout=30,
    )

    assert completed.returncode != 0
    assert "only valid in --diff-product or --product-mode" in completed.stdout


def test_llvm2bpl_pipeline_report_records_phases(tmp_path):
    source = "int f(int x) { return x + 1; }\n"
    report = tmp_path / "pipeline-report.json"
    completed = run_llvm2bpl(
        tmp_path,
        "pipeline_report",
        source,
        f"--smack-pipeline-report={report}",
    )

    assert completed.returncode == 0, completed.stdout
    data = json.loads(report.read_text())
    assert data["schema_version"] == 1
    assert data["llvm_version"]
    assert data["pipeline"] in {"legacy", "newpm"}
    assert data["input"].endswith("pipeline_report-linked.bc")
    assert data["outputs"]["bpl"].endswith("pipeline_report.bpl")
    assert data["outputs"]["ll"] is None
    assert data["options"]["modular"] is False
    assert data["options"]["static_unroll"] is False
    phase_names = [phase["name"] for phase in data["phases"]]
    assert "parse-ir" in phase_names
    if data["pipeline"] == "newpm":
        assert "newpm-full" in phase_names
        assert data["passes"]
    else:
        assert "pre-bpl" in phase_names
    assert all(phase["wall_ms"] >= 0 for phase in data["phases"])
    assert isinstance(data["passes"], list)


def test_llvm2bpl_default_memory_partitioner_is_sea_dsa(tmp_path):
    source = "int f(int x) { return x + 1; }\n"
    linked = compile_c_to_linked_bc(tmp_path, "default_memory_partitioner", source)
    report = tmp_path / "default_memory_partitioner.memory.json"

    completed = run_raw_llvm2bpl_on_linked(
        tmp_path,
        "default_memory_partitioner",
        linked,
        "f",
        f"--smack-memory-partition-report={report}",
    )

    assert completed.returncode == 0, completed.stdout
    parse_boogie((tmp_path / "default_memory_partitioner.bpl").read_text())
    data = json.loads(report.read_text())
    assert data["partitioner"] == "sea-dsa"


def test_llvm2bpl_svf_refined_accepts_v2_oracle_and_reports_frames(tmp_path):
    adapter = load_svf_adapter_module()
    source = "volatile int g;\nint f(int x) { g = x; return g; }\n"
    linked = compile_c_to_linked_bc(tmp_path, "svf_v2_oracle", source)
    pre_ll = tmp_path / "svf_v2_oracle.pre.ll"
    oracle_path = tmp_path / "svf_v2_oracle.oracle.json"
    report = tmp_path / "svf_v2_oracle.memory.json"

    pre = run_raw_llvm2bpl_on_linked(
        tmp_path,
        "svf_v2_oracle_pre",
        linked,
        "f",
        "-smack-memory-partitioner=sea-dsa",
        f"--ll={pre_ll}",
    )
    assert pre.returncode == 0, pre.stdout

    ll_text = pre_ll.read_text()
    oracle = adapter.build_oracle(
        ll_text=ll_text,
        svf_output=fake_svf_dump_for_function_accesses(adapter, ll_text, "f"),
    )
    oracle_path.write_text(json.dumps(oracle, indent=2, sort_keys=True) + "\n")

    completed = run_raw_llvm2bpl_on_linked(
        tmp_path,
        "svf_v2_oracle",
        linked,
        "f",
        "-smack-memory-partitioner=svf-refined",
        f"-smack-memory-partition-oracle={oracle_path}",
        f"--smack-memory-partition-report={report}",
    )

    assert completed.returncode == 0, completed.stdout
    data = json.loads(report.read_text())
    assert data["partitioner"] == "svf-refined"
    assert data["oracle_function_effect_count"] > 0
    assert data["oracle_frame_complete_count"] > 0
    assert data["oracle_frame_excluded_map_count"] >= 0


def test_llvm2bpl_svf_native_uses_inprocess_regions_without_dsa(tmp_path):
    source = """
volatile int g;
volatile int h;
int f(int x) {
  g = x;
  h = x + 1;
  return g + h;
}
"""
    linked = compile_c_to_linked_bc(tmp_path, "svf_native_regions", source)
    report = tmp_path / "svf_native_regions.memory.json"

    completed = run_llvm2bpl_on_linked(
        tmp_path,
        "svf_native_regions",
        linked,
        "f",
        "-smack-memory-partitioner=svf-native",
        f"--smack-memory-partition-report={report}",
    )

    if (
        completed.returncode != 0
        and "SMACK_ENABLE_INPROCESS_SVF=ON" in completed.stdout
    ):
        pytest.skip("llvm2bpl was built without in-process SVF")

    assert completed.returncode == 0, completed.stdout
    text = (tmp_path / "svf_native_regions.bpl").read_text()
    parse_boogie(text)
    data = json.loads(report.read_text())
    assert data["partitioner"] == "svf-native"
    assert data["dsa_mode"] == "none"
    assert data["oracle_access_count"] >= 4
    assert data["region_count"] >= 2
    assert data["oracle_noalias_count"] >= 1


def test_llvm2bpl_svf_refined_emits_complete_callsite_frame(tmp_path):
    adapter = load_svf_adapter_module()
    source = """
volatile int g;
volatile int h;
void touch(volatile int *p, int x) { *p = x; }
int f(int x) {
  h = 7;
  touch(&g, x);
  return h;
}
"""
    linked = compile_c_to_linked_bc(tmp_path, "svf_callsite_frame", source)
    pre_ll = tmp_path / "svf_callsite_frame.pre.ll"
    oracle_path = tmp_path / "svf_callsite_frame.oracle.json"
    report = tmp_path / "svf_callsite_frame.memory.json"

    pre = run_raw_llvm2bpl_on_linked(
        tmp_path,
        "svf_callsite_frame_pre",
        linked,
        "f",
        "-smack-memory-partitioner=sea-dsa",
        "-smack-skip-devirt",
        f"--ll={pre_ll}",
    )
    assert pre.returncode == 0, pre.stdout

    ll_text = pre_ll.read_text()
    oracle = adapter.build_oracle(
        ll_text=ll_text,
        svf_output=(
            fake_svf_dump_for_function_accesses(adapter, ll_text, "f", "MR_8")
            + fake_svf_dump_for_function_accesses(adapter, ll_text, "touch", "MR_9")
        ),
    )
    call = next(
        call
        for call in adapter.iter_module_call_infos(ll_text)
        if call.function == "f" and call.target == "touch"
    )
    oracle["callsite_effects"][call.key] = {
        "ref_regions": [],
        "mod_regions": ["MR_9"],
        "complete": True,
    }
    oracle_path.write_text(json.dumps(oracle, indent=2, sort_keys=True) + "\n")

    completed = run_raw_llvm2bpl_on_linked(
        tmp_path,
        "svf_callsite_frame",
        linked,
        "f",
        "-smack-memory-partitioner=svf-refined",
        f"-smack-memory-partition-oracle={oracle_path}",
        f"--smack-memory-partition-report={report}",
    )

    assert completed.returncode == 0, completed.stdout
    text = (tmp_path / "svf_callsite_frame.bpl").read_text()
    assert ".svf.call." in text
    assert re.search(r"call\s+[A-Za-z0-9_$@.]+\.svf\.call\.", text)
    parse_boogie(text)

    data = json.loads(report.read_text())
    assert data["oracle_callsite_effect_count"] >= 1
    assert data["oracle_frame_complete_count"] >= 1
    assert data["oracle_frame_excluded_map_count"] >= 1


def test_llvm2bpl_svf_refined_reports_loop_candidate_without_emitting_invariants(
    tmp_path,
):
    source = """
int f(int *a, int *b, int n) {
  int i = 0;
  *b = 7;
  while (i < n) {
    *a = i;
    i++;
  }
  return *b;
}
"""
    linked = compile_c_to_linked_bc(tmp_path, "svf_loop_candidate", source)
    oracle = build_empty_svf_oracle_for_linked(
        tmp_path, "svf_loop_candidate", linked, unique_accesses=True
    )
    oracle_path = tmp_path / "svf_loop_candidate.oracle.json"
    report = tmp_path / "svf_loop_candidate.memory.json"
    oracle_path.write_text(json.dumps(oracle, indent=2, sort_keys=True) + "\n")

    completed = run_llvm2bpl_on_linked(
        tmp_path,
        "svf_loop_candidate",
        linked,
        "f",
        "-smack-memory-partitioner=svf-refined",
        f"-smack-memory-partition-oracle={oracle_path}",
        f"--smack-memory-partition-report={report}",
    )

    assert completed.returncode == 0, completed.stdout
    text = (tmp_path / "svf_loop_candidate.bpl").read_text()
    assert ".svf.loop." not in text
    assert "invariant ($M." not in text

    data = json.loads(report.read_text())
    assert data["schema_version"] == 2
    candidates = data["svf_loop_candidates"]
    complete = [
        candidate
        for candidate in candidates
        if candidate["function"] == "f" and candidate["complete"]
    ]
    assert complete, data
    assert complete[0]["preserved_map_count"] >= 1
    assert complete[0]["retained_map_count"] >= 1
    assert complete[0]["mod_region_count"] >= 1
    assert complete[0]["fallback_reason"] == ""


def test_llvm2bpl_svf_refined_reports_incomplete_loop_candidate_reason(tmp_path):
    source = """
extern void opaque(int *);
int f(int *a, int n) {
  int i = 0;
  while (i < n) {
    opaque(a);
    i++;
  }
  return i;
}
"""
    linked = compile_c_to_linked_bc(tmp_path, "svf_loop_candidate_incomplete", source)
    oracle = build_empty_svf_oracle_for_linked(
        tmp_path, "svf_loop_candidate_incomplete", linked
    )
    oracle_path = tmp_path / "svf_loop_candidate_incomplete.oracle.json"
    report = tmp_path / "svf_loop_candidate_incomplete.memory.json"
    oracle_path.write_text(json.dumps(oracle, indent=2, sort_keys=True) + "\n")

    completed = run_llvm2bpl_on_linked(
        tmp_path,
        "svf_loop_candidate_incomplete",
        linked,
        "f",
        "-smack-memory-partitioner=svf-refined",
        f"-smack-memory-partition-oracle={oracle_path}",
        f"--smack-memory-partition-report={report}",
    )

    assert completed.returncode == 0, completed.stdout
    data = json.loads(report.read_text())
    incomplete = [
        candidate
        for candidate in data["svf_loop_candidates"]
        if candidate["function"] == "f" and not candidate["complete"]
    ]
    assert incomplete, data
    assert incomplete[0]["fallback_reason"] == "unknown-external-call-effect"
    assert incomplete[0]["retained_map_count"] >= 1


def test_paired_structured_loop_can_emit_svf_loop_frame_invariants(tmp_path):
    source = """
int f(int *a, int *b, int n) {
  int i = 0;
  *b = 7;
  while (i < n) {
    *a = i;
    i++;
  }
  return *b;
}
"""
    left = compile_c_to_linked_bc(tmp_path, "svf_loop_frame_left", source)
    right = compile_c_to_linked_bc(tmp_path, "svf_loop_frame_right", source)
    oracle = write_bundled_svf_oracle(
        tmp_path, "svf_loop_frame", left, right, unique_accesses=True
    )
    left_bpl = tmp_path / "svf_loop_frame_left.bpl"
    right_bpl = tmp_path / "svf_loop_frame_right.bpl"
    match_json = tmp_path / "svf_loop_frame_match.json"

    completed = run_with_timeout(
        [
            tool_path("llvm-diffmatch2bpl"),
            "--left-bc",
            str(left),
            "--right-bc",
            str(right),
            "--left-entry",
            "f",
            "--right-entry",
            "f",
            "--left-bpl",
            str(left_bpl),
            "--right-bpl",
            str(right_bpl),
            "--match-json",
            str(match_json),
            "-entry-points",
            "f",
            "--structured-bpl-loops-strict",
            "-smack-svf-loop-frames",
            "-smack-memory-partitioner=svf-refined",
            f"-smack-memory-partition-oracle={oracle}",
        ],
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        check=False,
        timeout_name="SMACK_TOOL",
        default_timeout=120,
    )

    assert completed.returncode == 0, completed.stdout
    text = left_bpl.read_text()
    assert ".svf.loop." in text
    assert "invariant ($M." in text
    parse_boogie(text)


def test_llvm2bpl_memory_partition_report_records_regions(tmp_path):
    source = """
#include <stdlib.h>
struct Cell {
  int value;
};
int f(int x) {
  struct Cell *cell = malloc(sizeof(struct Cell));
  cell->value = x + 1;
  return cell->value;
}
"""
    report = tmp_path / "memory-partition-report.json"
    completed = run_llvm2bpl(
        tmp_path,
        "memory_report",
        source,
        f"--smack-memory-partition-report={report}",
    )

    assert completed.returncode == 0, completed.stdout
    data = json.loads(report.read_text())
    assert data["schema_version"] == 2
    assert data["llvm_version"]
    assert data["pipeline"] in {"legacy", "newpm"}
    assert data["partitioner"] == "sea-dsa"
    assert data["dsa_mode"] == "bu"
    assert data["region_count"] > 0
    assert data["memory_access_count"] > 0
    assert set(data["regions"]) == {
        "singleton",
        "allocated",
        "bytewise",
        "incomplete",
        "complicated",
        "collapsed",
        "typed",
        "untyped",
    }
    assert all(value >= 0 for value in data["regions"].values())
    assert isinstance(data["fallback_reasons"], list)


def test_llvm2bpl_accepts_all_sea_dsa_modes(tmp_path):
    source = """
int f(int x) {
  int a = x;
  int b = a + 1;
  return b;
}
"""
    linked = compile_c_to_linked_bc(tmp_path, "sea_dsa_modes", source)

    for mode in ("bu", "butd-cs", "cs", "flat"):
        report = tmp_path / f"{mode}.json"
        completed = run_llvm2bpl_on_linked(
            tmp_path,
            f"sea_dsa_{mode}",
            linked,
            "f",
            f"-sea-dsa={mode}",
            f"--smack-memory-partition-report={report}",
        )
        assert completed.returncode == 0, completed.stdout
        data = json.loads(report.read_text())
        assert data["partitioner"] == "sea-dsa"
        assert data["dsa_mode"] == mode


@pytest.mark.parametrize("partitioner", ["cell-refined", "aa-refined"])
def test_llvm2bpl_memory_partitioner_is_reported(tmp_path, partitioner):
    source = """
int f(int x) {
  int a = x;
  int *p = &a;
  *p = *p + 1;
  return a;
}
"""
    report = tmp_path / f"{partitioner}.json"
    completed = run_llvm2bpl(
        tmp_path,
        partitioner.replace("-", "_"),
        source,
        f"-smack-memory-partitioner={partitioner}",
        f"--smack-memory-partition-report={report}",
    )

    assert completed.returncode == 0, completed.stdout
    data = json.loads(report.read_text())
    assert data["partitioner"] == partitioner
    assert data["dsa_mode"] == "bu"


@pytest.mark.parametrize(
    "name, source, min_while_count",
    [
        (
            "nested",
            """
int f(int n) {
  int i = 0;
  int s = 0;
  while (i < n) {
    int j = 0;
    while (j < i) {
      s += j;
      j++;
    }
    i++;
  }
  return s;
}
""",
            2,
        ),
        (
            "continue_loop",
            """
int f(int n) {
  int i = 0;
  int s = 0;
  while (i < n) {
    i++;
    if (i == 3) continue;
    s += i;
  }
  return s;
}
""",
            1,
        ),
        (
            "break_loop",
            """
int f(int n) {
  int i = 0;
  int s = 0;
  while (i < n) {
    if (i == 3) break;
    s += i;
    i++;
  }
  return s;
}
""",
            1,
        ),
        (
            "branchy_loop",
            """
int f(int n) {
  int i = 0;
  int s = 0;
  while (i < n) {
    if ((i & 1) == 0) {
      s += i;
    } else {
      s -= i;
    }
    i++;
  }
  return s;
}
""",
            1,
        ),
    ],
)
def test_structured_bpl_loops_handle_common_reducible_shapes(
    tmp_path, name, source, min_while_count
):
    structured, _, _ = emit_paired_product_bpl(
        tmp_path, name, source, "--structured-bpl-loops-strict"
    )

    assert structured.count("while (true)") >= min_while_count
    assert_structured_boogie(structured)

import importlib.util
import json
import sys

import pytest
from smack_test_paths import REPO_ROOT


def load_compare_module():
    module_path = REPO_ROOT / "tools" / "memory_partition_compare.py"
    spec = importlib.util.spec_from_file_location("memory_partition_compare", module_path)
    assert spec is not None
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def make_report(**overrides):
    report = {
        "schema_version": 1,
        "llvm_version": "22.1.3",
        "pipeline": "legacy",
        "input": "fixture.bc",
        "partitioner": "sea-dsa",
        "dsa_mode": "bu",
        "region_count": 3,
        "memory_access_count": 10,
        "merge_count": 1,
        "late_region_count": 0,
        "regions": {
            "singleton": 1,
            "allocated": 2,
            "bytewise": 0,
            "incomplete": 0,
            "complicated": 0,
            "collapsed": 0,
            "typed": 3,
            "untyped": 0,
        },
        "fallback_reasons": [],
    }
    report.update(overrides)
    return report


def test_load_memory_report_validates_schema_and_metrics(tmp_path):
    compare = load_compare_module()
    report = tmp_path / "memory.json"
    report.write_text(
        """
        {
          "schema_version": 1,
          "llvm_version": "22.1.3",
          "pipeline": "legacy",
          "input": "x.bc",
          "partitioner": "cell-refined",
          "dsa_mode": "butd-cs",
          "region_count": 4,
          "memory_access_count": 11,
          "merge_count": 2,
          "late_region_count": 1,
          "regions": {
            "singleton": 1,
            "allocated": 2,
            "bytewise": 0,
            "incomplete": 1,
            "complicated": 0,
            "collapsed": 0,
            "typed": 3,
            "untyped": 1
          },
          "fallback_reasons": [
            {"name": "incomplete", "count": 1},
            {"name": "untyped", "count": 1}
          ]
        }
        """
    )

    loaded = compare.load_memory_report(report)

    assert compare.fallback_total(loaded) == 2
    assert compare.imprecise_region_count(loaded) == 2
    assert compare.precision_metrics(loaded)["region_count"] == 4


def test_load_memory_report_rejects_wrong_schema(tmp_path):
    compare = load_compare_module()
    report = tmp_path / "memory.json"
    report.write_text('{"schema_version": 99}')

    with pytest.raises(compare.CompareError, match="unsupported memory report schema"):
        compare.load_memory_report(report)


def test_parse_candidate_splits_shell_flags():
    compare = load_compare_module()
    candidate = compare.parse_candidate(
        "cell-refined=-sea-dsa=butd-cs -smack-memory-partitioner=cell-refined"
    )

    assert candidate.label == "cell-refined"
    assert candidate.flags == ("-sea-dsa=butd-cs", "-smack-memory-partitioner=cell-refined")


def test_parse_bc_fixture_marks_bitcode_and_runtime_policy():
    compare = load_compare_module()

    fixture = compare.parse_bc_fixture("bearssl=target/bearssl.bc:entry", link_runtime=False)

    assert fixture.label == "bearssl"
    assert fixture.source.as_posix() == "target/bearssl.bc"
    assert fixture.entry_point == "entry"
    assert fixture.kind == "bitcode"
    assert fixture.link_runtime is False


def test_parse_external_probe_splits_candidate_tools():
    compare = load_compare_module()

    probe = compare.parse_external_probe("svf=wpa,svf-ex")

    assert probe.label == "svf"
    assert probe.tools == ("wpa", "svf-ex")


def test_svf_refined_candidate_without_oracle_uses_generated_oracle_path():
    compare = load_compare_module()

    needs_oracle = compare.parse_candidate(
        "svf-refined-bu=-sea-dsa=bu -smack-memory-partitioner=svf-refined"
    )
    has_oracle = compare.parse_candidate(
        "svf-refined-bu=-sea-dsa=bu -smack-memory-partitioner=svf-refined "
        "-smack-memory-partition-oracle=oracle.json"
    )

    assert compare._requires_generated_svf_refined_oracle(needs_oracle)
    assert not compare._requires_generated_svf_refined_oracle(has_oracle)


def test_count_boogie_memory_maps_counts_global_memory_declarations(tmp_path):
    compare = load_compare_module()
    bpl = tmp_path / "fixture.bpl"
    bpl.write_text(
        "\n".join(
            [
                "var $M.0: [ref] i8;",
                "  var $M.1_local: ref;",
                "var $M.1: [ref] i32;",
                "const unique $M.foo: ref;",
            ]
        )
    )

    assert compare.count_boogie_memory_maps(bpl) == 2


def test_rank_candidates_prioritizes_memory_maps_then_diagnostics():
    compare = load_compare_module()
    fewer_maps = make_report(region_count=5, regions={**make_report()["regions"], "typed": 5})
    coarse = make_report(region_count=3)
    more_maps_with_fallback = make_report(
        region_count=20,
        regions={**make_report()["regions"], "untyped": 1},
        fallback_reasons=[{"name": "untyped", "count": 1}],
    )
    records = [
        {
            "candidate": "fewer-maps",
            "status": "ok",
            "wall_ms": 10.0,
            "metrics": compare.precision_metrics(fewer_maps, memory_map_count=5),
        },
        {
            "candidate": "coarse",
            "status": "ok",
            "wall_ms": 10.0,
            "metrics": compare.precision_metrics(coarse, memory_map_count=3),
        },
        {
            "candidate": "more-maps-with-fallback",
            "status": "ok",
            "wall_ms": 1.0,
            "metrics": compare.precision_metrics(
                more_maps_with_fallback, memory_map_count=20
            ),
        },
    ]

    ranking = compare.rank_candidates(records)

    assert [item["candidate"] for item in ranking] == [
        "more-maps-with-fallback",
        "fewer-maps",
        "coarse",
    ]


def test_rank_candidates_prefers_more_memory_maps():
    compare = load_compare_module()
    report = make_report(region_count=5, regions={**make_report()["regions"], "typed": 5})
    records = [
        {
            "candidate": "fewer-maps",
            "status": "ok",
            "wall_ms": 1.0,
            "metrics": compare.precision_metrics(report, memory_map_count=2),
        },
        {
            "candidate": "more-maps",
            "status": "ok",
            "wall_ms": 1.0,
            "metrics": compare.precision_metrics(report, memory_map_count=7),
        },
    ]

    ranking = compare.rank_candidates(records)

    assert [item["candidate"] for item in ranking] == ["more-maps", "fewer-maps"]


def test_rank_candidates_uses_fallback_after_memory_map_tie():
    compare = load_compare_module()
    clean = make_report(region_count=5, regions={**make_report()["regions"], "typed": 5})
    fallback = make_report(
        region_count=5,
        regions={**make_report()["regions"], "untyped": 1, "typed": 5},
        fallback_reasons=[{"name": "untyped", "count": 1}],
    )
    records = [
        {
            "candidate": "fallback",
            "status": "ok",
            "wall_ms": 1.0,
            "metrics": compare.precision_metrics(fallback, memory_map_count=7),
        },
        {
            "candidate": "clean",
            "status": "ok",
            "wall_ms": 1.0,
            "metrics": compare.precision_metrics(clean, memory_map_count=7),
        },
    ]

    ranking = compare.rank_candidates(records)

    assert [item["candidate"] for item in ranking] == ["clean", "fallback"]


def test_parse_svf_mssa_metrics_extracts_partition_stats():
    compare = load_compare_module()
    output = """
*********Memory SSA Statistics***************
################ (program : fixture.bc)###############
----------------Time and memory stats--------------------
AverageRegSize      1.75
TotalMSSATime       0.025
----------------Numbers stats----------------------------
LoadMuNode          17
MSSAPhi             3
MaxRegSize          4
MemRegions          9
StoreChiNode        11
#######################################################
*********SVFG Statistics***************
"""

    metrics = compare.parse_svf_mssa_metrics(output)

    assert metrics["memory_region_count"] == 9
    assert metrics["average_region_size"] == 1.75
    assert metrics["max_region_size"] == 4
    assert metrics["load_mu_node_count"] == 17
    assert metrics["store_chi_node_count"] == 11
    assert metrics["mssa_phi_count"] == 3
    assert metrics["total_mssa_time"] == 0.025


def test_rank_external_candidates_prioritizes_more_svf_regions():
    compare = load_compare_module()
    records = [
        {
            "candidate": "svf-andersen-intra-disjoint",
            "status": "ok",
            "wall_ms": 2.0,
            "metrics": {
                "memory_region_count": 8,
                "average_region_size": 1.0,
                "max_region_size": 1,
                "load_mu_node_count": 10,
                "store_chi_node_count": 5,
                "mssa_phi_count": 1,
                "total_mssa_time": 0.02,
            },
        },
        {
            "candidate": "svf-andersen-distinct",
            "status": "ok",
            "wall_ms": 3.0,
            "metrics": {
                "memory_region_count": 12,
                "average_region_size": 1.0,
                "max_region_size": 1,
                "load_mu_node_count": 12,
                "store_chi_node_count": 6,
                "mssa_phi_count": 1,
                "total_mssa_time": 0.03,
            },
        },
    ]

    ranking = compare.rank_external_candidates(records)

    assert [item["candidate"] for item in ranking] == [
        "svf-andersen-distinct",
        "svf-andersen-intra-disjoint",
    ]


def test_build_summary_and_markdown_include_bitcode_fixture_and_maps(tmp_path):
    compare = load_compare_module()
    fixture = compare.parse_bc_fixture("bearssl=/tmp/bearssl.bc:entry")
    candidate = compare.parse_candidate("ci=-sea-dsa=ci")
    report = make_report(region_count=5, regions={**make_report()["regions"], "typed": 5})
    records = [
        {
            "candidate": "ci",
            "fixture": "bearssl",
            "status": "ok",
            "wall_ms": 1.0,
            "metrics": compare.precision_metrics(report, memory_map_count=11),
        }
    ]

    summary = compare.build_summary(
        repo_root=REPO_ROOT,
        llvm2bpl=REPO_ROOT / "build-llvm22c" / "llvm2bpl",
        clang=REPO_ROOT / "build-llvm22c" / "clang",
        llvm_link=REPO_ROOT / "build-llvm22c" / "llvm-link",
        fixtures=[fixture],
        candidates=[candidate],
        records=records,
        external_probes=[compare.parse_external_probe("svf=definitely-not-installed-svf")],
        external_records=[],
    )
    md = tmp_path / "summary.md"
    compare.write_markdown(summary, md)

    assert summary["fixtures"][0]["kind"] == "bitcode"
    assert summary["fixtures"][0]["link_runtime"] is True
    assert summary["ranking"][0]["metrics"]["memory_map_count"] == 11
    text = md.read_text()
    assert "| Rank | Candidate | OK | Fail | Fallback | Imprecise | Maps |" in text
    assert "## External Candidate Probes" in text
    assert summary["external_candidates"][0]["candidate"] == "svf"
    assert summary["external_candidates"][0]["status"] == "skipped"


def test_run_svf_refined_candidate_generates_oracle_and_counts_maps(monkeypatch, tmp_path):
    compare = load_compare_module()
    fixture = compare.Fixture(label="tiny", source=tmp_path / "tiny.bc", entry_point="main")
    fixture.source.write_text("not really bitcode")
    calls = []

    def fake_run_command(args, *, cwd, timeout, check=True):
        calls.append(args)
        if any(str(arg).startswith("--ll=") for arg in args):
            ll_path = next(
                str(arg).split("=", 1)[1] for arg in args if str(arg).startswith("--ll=")
            )
            (tmp_path / "unused").mkdir(exist_ok=True)
            compare.Path(ll_path).write_text(
                """
define dso_local i32 @main() {
  %2 = load i32, ptr %1, align 4
  ret i32 %2
}
"""
            )
            return compare.subprocess.CompletedProcess(args, 0, "")
        if len(args) > 1 and str(args[1]).endswith("svf_memory_partition_adapter.py"):
            out_path = compare.Path(args[args.index("--out") + 1])
            out_path.write_text(
                json.dumps(
                    {
                        "schema_version": 1,
                        "producer": "svf-memory-partition-adapter",
                        "analysis": "andersen",
                        "module_fingerprint": "0" * 16,
                        "access_regions": {},
                    }
                )
            )
            return compare.subprocess.CompletedProcess(args, 0, "")

        report_path = compare.Path(
            next(
                str(arg).split("=", 1)[1]
                for arg in args
                if str(arg).startswith("--smack-memory-partition-report=")
            )
        )
        bpl_path = compare.Path(
            next(str(arg).split("=", 1)[1] for arg in args if str(arg).startswith("--bpl="))
        )
        report_path.write_text(json.dumps(make_report(region_count=3)))
        bpl_path.write_text("var $M.0: [ref] i32;\nvar $M.1: [ref] i32;\n")
        return compare.subprocess.CompletedProcess(args, 0, "")

    monkeypatch.setattr(compare, "run_command", fake_run_command)

    record = compare._run_svf_refined_candidate(
        llvm2bpl=tmp_path / "llvm2bpl",
        linked_bc=fixture.source,
        fixture=fixture,
        svf_wpa=tmp_path / "wpa",
        svf_extapi=tmp_path / "extapi.bc",
        mem_par="intra-disjoint",
        repo_root=REPO_ROOT,
        out_dir=tmp_path,
        timeout=30,
    )

    assert record["status"] == "ok"
    assert record["candidate"] == "svf-refined-bu"
    assert record["metrics"]["memory_map_count"] == 2
    assert len(calls) == 3
    assert any(str(arg).startswith("--ll=") for arg in calls[0])
    assert calls[1][1].endswith("svf_memory_partition_adapter.py")
    assert "-smack-skip-pre-bpl" not in calls[2]
    assert "-smack-memory-partitioner=svf-refined" in calls[2]
    assert str(calls[2][-1]).endswith("tiny.bc")

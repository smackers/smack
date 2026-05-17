import importlib.util
import json
import sys

import pytest
from smack_test_paths import REPO_ROOT


def load_compare_module():
    module_path = REPO_ROOT / "tools" / "devirt_compare.py"
    spec = importlib.util.spec_from_file_location("devirt_compare", module_path)
    assert spec is not None
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def make_callsite(**overrides):
    callsite = {
        "callsite_id": "f:indirect:0",
        "callsite_index": 0,
        "function": "f",
        "file": "fixture.c",
        "line": 10,
        "column": 3,
        "instruction": "%r = call i32 %fp(i32 %x)",
        "sea_dsa_complete": False,
        "complete": True,
        "sea_dsa_target_count": 0,
        "fallback_target_count": 2,
        "target_count": 1,
        "source": "type-dataflow",
        "reason": "constant-function",
        "targets": ["only"],
    }
    callsite.update(overrides)
    return callsite


def make_report(*callsites):
    return {
        "schema_version": 2,
        "module": "fixture.bc",
        "callsites": list(callsites) or [make_callsite()],
    }


def test_load_devirt_report_validates_and_normalizes_schema_v2(tmp_path):
    compare = load_compare_module()
    report = tmp_path / "devirt.json"
    report.write_text(json.dumps(make_report(make_callsite(targets=["z", "z", "a"]))))

    loaded = compare.load_devirt_report(report)

    assert loaded["schema_version"] == 2
    assert loaded["callsites"][0]["callsite_id"] == "f:indirect:0"
    assert loaded["callsites"][0]["targets"] == ["a", "z"]
    assert loaded["callsites"][0]["target_count"] == 2


def test_load_devirt_report_synthesizes_ids_for_schema_v1(tmp_path):
    compare = load_compare_module()
    report = tmp_path / "devirt-v1.json"
    callsite = make_callsite()
    del callsite["callsite_id"]
    del callsite["callsite_index"]
    report.write_text(json.dumps({"schema_version": 1, "callsites": [callsite]}))

    loaded = compare.load_devirt_report(report)

    assert loaded["callsites"][0]["callsite_id"] == "f:indirect:0"
    assert loaded["callsites"][0]["callsite_index"] == 0


def test_load_devirt_report_rejects_wrong_schema(tmp_path):
    compare = load_compare_module()
    report = tmp_path / "devirt.json"
    report.write_text('{"schema_version": 99, "callsites": []}')

    with pytest.raises(compare.CompareError, match="unsupported devirt report schema"):
        compare.load_devirt_report(report)


def test_devirt_metrics_count_complete_singleton_and_fallback():
    compare = load_compare_module()
    report = make_report(
        make_callsite(callsite_id="f:indirect:0", complete=True, targets=["only"]),
        make_callsite(
            callsite_id="f:indirect:1",
            callsite_index=1,
            complete=False,
            source="fallback",
            targets=["only", "other"],
            fallback_target_count=2,
        ),
    )

    metrics = compare.devirt_metrics(report)

    assert metrics["total_callsites"] == 2
    assert metrics["complete_callsites"] == 1
    assert metrics["singleton_callsites"] == 1
    assert metrics["fallback_callsites"] == 1
    assert metrics["fallback_target_total"] == 4
    assert metrics["oracle_callsites"] == 0


def test_rank_candidates_prefers_more_complete_then_singleton_then_smaller_sets():
    compare = load_compare_module()
    records = [
        {
            "candidate": "coarse",
            "status": "ok",
            "wall_ms": 1.0,
            "metrics": {
                "total_callsites": 2,
                "complete_callsites": 2,
                "incomplete_callsites": 0,
                "fallback_callsites": 0,
                "singleton_callsites": 0,
                "target_total": 4,
                "complete_target_total": 4,
                "fallback_target_total": 0,
                "max_target_count": 2,
            },
        },
        {
            "candidate": "precise",
            "status": "ok",
            "wall_ms": 5.0,
            "metrics": {
                "total_callsites": 2,
                "complete_callsites": 2,
                "incomplete_callsites": 0,
                "fallback_callsites": 0,
                "singleton_callsites": 2,
                "target_total": 2,
                "complete_target_total": 2,
                "fallback_target_total": 0,
                "max_target_count": 1,
            },
        },
        {
            "candidate": "fallback",
            "status": "ok",
            "wall_ms": 1.0,
            "metrics": {
                "total_callsites": 2,
                "complete_callsites": 1,
                "incomplete_callsites": 1,
                "fallback_callsites": 1,
                "singleton_callsites": 1,
                "target_total": 3,
                "complete_target_total": 1,
                "fallback_target_total": 2,
                "max_target_count": 2,
            },
        },
    ]

    ranking = compare.rank_candidates(records)

    assert [item["candidate"] for item in ranking] == ["precise", "coarse", "fallback"]


def test_rank_candidates_prefers_sound_oracle_over_smaller_wrong_set():
    compare = load_compare_module()
    base_metrics = {
        "total_callsites": 1,
        "complete_callsites": 1,
        "incomplete_callsites": 0,
        "fallback_callsites": 0,
        "fallback_target_total": 0,
        "max_target_count": 1,
    }
    records = [
        {
            "candidate": "wrong-singleton",
            "status": "ok",
            "wall_ms": 1.0,
            "metrics": {
                **base_metrics,
                "singleton_callsites": 1,
                "target_total": 1,
                "complete_target_total": 1,
                "oracle_callsites": 1,
                "oracle_sound_callsites": 0,
                "oracle_exact_callsites": 0,
                "oracle_unsound_callsites": 1,
                "oracle_missing_target_total": 4,
                "oracle_spurious_target_total": 1,
            },
        },
        {
            "candidate": "sound-coarse",
            "status": "ok",
            "wall_ms": 2.0,
            "metrics": {
                **base_metrics,
                "singleton_callsites": 0,
                "target_total": 8,
                "complete_target_total": 8,
                "max_target_count": 8,
                "oracle_callsites": 1,
                "oracle_sound_callsites": 1,
                "oracle_exact_callsites": 0,
                "oracle_unsound_callsites": 0,
                "oracle_missing_target_total": 0,
                "oracle_spurious_target_total": 4,
            },
        },
    ]

    ranking = compare.rank_candidates(records)

    assert [item["candidate"] for item in ranking] == ["sound-coarse", "wrong-singleton"]


def test_bearssl_oracle_marks_exact_missing_and_spurious_targets():
    compare = load_compare_module()
    report = make_report(
        make_callsite(
            callsite_id="bearssl_devirt_hash_entry:indirect:0",
            function="bearssl_devirt_hash_entry",
            line=69,
            targets=["br_ssl_hs_client_run"],
        ),
        make_callsite(
            callsite_id="bearssl_devirt_hash_entry:indirect:1",
            callsite_index=1,
            function="bearssl_devirt_hash_entry",
            line=70,
            targets=[
                "br_md5sha1_update",
                "br_sha1_update",
                "br_sha224_update",
                "br_sha384_update",
            ],
        ),
    )

    annotated = compare.annotate_report_with_oracle(report, fixture="bearssl")
    metrics = compare.devirt_metrics(annotated)

    first, second = annotated["callsites"]
    assert first["oracle_sound"] is False
    assert first["missing_targets"] == [
        "br_md5sha1_init",
        "br_sha1_init",
        "br_sha256_init",
        "br_sha512_init",
    ]
    assert first["spurious_targets"] == ["br_ssl_hs_client_run"]
    assert second["oracle_exact"] is True
    assert metrics["oracle_callsites"] == 2
    assert metrics["oracle_sound_callsites"] == 1
    assert metrics["oracle_exact_callsites"] == 1


def test_svf_flags_follow_candidate_label():
    compare = load_compare_module()

    assert compare.svf_flags_for_candidate("svf") == ("-ander",)
    assert compare.svf_flags_for_candidate("svf-sfrander") == ("-sfrander",)
    assert compare.svf_flags_for_candidate("svf-ander-model-arrays") == (
        "-ander",
        "-model-arrays",
    )
    assert compare.svf_flags_for_candidate("svf-local-ander-model-arrays") == (
        "-ander",
        "-model-arrays",
    )


def test_default_external_svf_candidate_is_local_ander():
    compare = load_compare_module()

    assert compare.DEFAULT_EXTERNAL_CANDIDATES[0].startswith("svf-local-ander=")
    assert not any(
        spec.startswith("svf-ander=") for spec in compare.DEFAULT_EXTERNAL_CANDIDATES
    )
    assert not any(
        spec.startswith("svf-local-ander-model-arrays=")
        for spec in compare.DEFAULT_EXTERNAL_CANDIDATES
    )


def test_parse_candidate_and_external_specs():
    compare = load_compare_module()

    candidate = compare.parse_candidate("sea=-sea-dsa=butd-cs -sea-dsa-type-aware")
    external = compare.parse_external_candidate("svf=wpa,svf-ex")
    fixture = compare.parse_bc_fixture("bearssl=build/bearssl.bc:bearssl_devirt_entry")
    external_input = compare.parse_external_input("svf:bearssl=build/svf-bearssl.bc")

    assert candidate.flags == ("-sea-dsa=butd-cs", "-sea-dsa-type-aware")
    assert external.tools == ("wpa", "svf-ex")
    assert fixture.kind == "bitcode"
    assert fixture.entry_point == "bearssl_devirt_entry"
    assert external_input.candidate == "svf"
    assert external_input.fixture == "bearssl"
    assert external_input.path.as_posix() == "build/svf-bearssl.bc"


def test_resolve_external_tool_prefers_analyzer_manifest(tmp_path):
    compare = load_compare_module()
    tool = tmp_path / "bin" / "wpa"
    tool.parent.mkdir()
    tool.write_text("#!/bin/sh\n")
    manifest = tmp_path / "manifest.json"
    manifest.write_text(
        json.dumps(
            {
                "schema_version": 1,
                "analyzers": {
                    "svf": {
                        "status": "available",
                        "tools": {"wpa": str(tool)},
                    }
                },
            }
        )
    )

    loaded = compare.load_analyzer_manifest(manifest, repo_root=REPO_ROOT)
    resolved = compare.resolve_external_tool(
        compare.parse_external_candidate("svf-ander=wpa,svf-ex"),
        repo_root=REPO_ROOT,
        manifest=loaded,
    )

    assert resolved == tool.resolve()


def test_manifest_svf_extapi_finds_installed_runtime(tmp_path):
    compare = load_compare_module()
    extapi = tmp_path / "svf" / "install" / "lib" / "extapi.bc"
    extapi.parent.mkdir(parents=True)
    extapi.write_text("")
    manifest = {
        "analyzers": {
            "svf": {
                "install_dir": str(tmp_path / "svf" / "install"),
                "tools": {},
            }
        }
    }

    resolved = compare._manifest_svf_extapi(
        compare.parse_external_candidate("svf-ander=wpa"),
        repo_root=REPO_ROOT,
        manifest=manifest,
    )

    assert resolved == extapi.resolve()


def test_canonicalize_external_report_matches_callsite_id():
    compare = load_compare_module()
    inventory = make_report(make_callsite())
    observation = compare.ExternalObservation(
        callsite_id="f:indirect:0",
        targets=("only",),
    )

    report = compare.canonicalize_external_report(
        inventory=inventory,
        observations=[observation],
        candidate="svf-ander",
        adapter="svf",
    )

    assert report["candidate"] == "svf-ander"
    assert report["callsites"][0]["complete"] is True
    assert report["callsites"][0]["source"] == "svf"
    assert report["callsites"][0]["targets"] == ["only"]


def test_parse_svf_output_extracts_targets():
    compare = load_compare_module()
    output = """
NodeID: 42
CallSite: %r = call i32 %fp(i32 %x) Location: fixture.c:10:3 with Targets: @only @other
"""

    observations = compare.parse_svf_output(output)

    assert len(observations) == 1
    assert observations[0].line == 10
    assert observations[0].targets == ("only", "other")


def test_parse_svf_output_extracts_multiline_targets():
    compare = load_compare_module()
    output = """
NodeID: 80727
CallSite: CallICFGNode69522 {fun: br_ssl_engine_init_rand{ "ln": 527, "cl": 18, "fl": "src/ssl/ssl_engine.c" }}
   %23 = call i32 %19(%struct.prng** %22), !dbg !1 CallICFGNode: { "ln": 527, "cl": 18, "fl": "src/ssl/ssl_engine.c" }\tLocation: CallICFGNode: { "ln": 527, "cl": 18, "fl": "src/ssl/ssl_engine.c" }\t with Targets:
\tseeder_getentropy
NodeID: 82430
"""

    observations = compare.parse_svf_output(output)

    assert len(observations) == 1
    assert observations[0].function == "br_ssl_engine_init_rand"
    assert observations[0].file == "src/ssl/ssl_engine.c"
    assert observations[0].line == 527
    assert observations[0].targets == ("seeder_getentropy",)


def test_parse_phasar_results_extracts_edges():
    compare = load_compare_module()
    data = {
        "callgraph": [
            {"callsite": "%r = call i32 %fp(i32 %x)", "callee": "only"},
            {"callsite": "%r = call i32 %fp(i32 %x)", "callee": "other"},
        ]
    }

    observations = compare.parse_phasar_results(data)

    assert len(observations) == 1
    assert observations[0].targets == ("only", "other")


def test_parse_phasar_callgraph_json_extracts_line_observations():
    compare = load_compare_module()
    data = {"only": [10], "other": [10], "__psrCRuntimeGlobalCtorsModel": None}

    observations = compare.parse_phasar_callgraph_json(data)

    assert len(observations) == 1
    assert observations[0].line == 10
    assert observations[0].targets == ("only", "other")


def test_canonicalize_external_report_matches_unique_line():
    compare = load_compare_module()
    inventory = make_report(make_callsite())
    observation = compare.ExternalObservation(line=10, targets=("only",))

    report = compare.canonicalize_external_report(
        inventory=inventory,
        observations=[observation],
        candidate="phasar-vta",
        adapter="phasar",
    )

    assert report["callsites"][0]["complete"] is True
    assert report["callsites"][0]["targets"] == ["only"]


def test_canonicalize_external_devirt_report_preserves_svf_local_incomplete():
    compare = load_compare_module()
    inventory = make_report(make_callsite())
    raw = make_report(
        make_callsite(
            complete=False,
            source="svf-local-slot",
            reason="svf-local-unhandled-points-to-object",
            targets=["maybe"],
            points_to_count=2,
            svf_unhandled_object_count=1,
        )
    )

    report = compare.canonicalize_external_devirt_report(
        inventory=inventory,
        report=raw,
        candidate="svf-local-ander",
        adapter="svf-local-slot",
    )

    call = report["callsites"][0]
    assert call["complete"] is False
    assert call["source"] == "svf-local-slot"
    assert call["reason"] == "svf-local-unhandled-points-to-object"
    assert call["targets"] == ["maybe"]
    assert call["points_to_count"] == 2
    assert call["svf_unhandled_object_count"] == 1


def test_build_summary_and_markdown_include_bearssl_and_external(tmp_path):
    compare = load_compare_module()
    fixture = compare.parse_bc_fixture("bearssl=/tmp/bearssl.bc:bearssl_devirt_entry")
    candidate = compare.parse_candidate("smack-default=")
    report = make_report(make_callsite())
    records = [
        {
            "fixture": "bearssl",
            "candidate": "smack-default",
            "status": "ok",
            "wall_ms": 1.0,
            "report": report,
            "metrics": compare.devirt_metrics(report),
        }
    ]

    summary = compare.build_summary(
        repo_root=REPO_ROOT,
        llvm2bpl=REPO_ROOT / "build-llvm22c" / "llvm2bpl",
        clang=REPO_ROOT / "build-llvm22c" / "clang",
        llvm_link=REPO_ROOT / "build-llvm22c" / "llvm-link",
        llvm_dis=REPO_ROOT / "build-llvm22c" / "llvm-dis",
        fixtures=[fixture],
        candidates=[candidate],
        external_candidates=[compare.parse_external_candidate("svf=wpa,svf-ex")],
        analyzer_manifest=None,
        external_inputs={},
        records=records,
    )
    md = tmp_path / "devirt.md"
    compare.write_markdown(summary, md)

    assert summary["fixtures"][0]["label"] == "bearssl"
    assert summary["external_candidates"][0]["label"] == "svf"
    text = md.read_text()
    assert "# SMACK Devirtualization Comparison" in text
    assert "## Per-Callsite Comparison" in text
    assert "`f:indirect:0`" in text

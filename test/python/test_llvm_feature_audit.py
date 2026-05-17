import importlib.util
import sys

import pytest
from smack_test_paths import REPO_ROOT


def load_audit_module():
    module_path = REPO_ROOT / "tools" / "llvm_feature_audit.py"
    spec = importlib.util.spec_from_file_location("llvm_feature_audit", module_path)
    assert spec is not None
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def test_load_pipeline_report_validates_and_extracts_timings(tmp_path):
    audit = load_audit_module()
    report = tmp_path / "report.json"
    report.write_text(
        """
        {
          "schema_version": 1,
          "phases": [
            {"name": "parse-ir", "wall_ms": 1.25},
            {"name": "newpm-full", "wall_ms": 3.50}
          ],
          "passes": [
            {"name": "SlowPass", "ir_unit": "module", "wall_ms": 2.0, "skipped": false},
            {"name": "SkippedPass", "ir_unit": "function", "wall_ms": 0.0, "skipped": true},
            {"name": "FastPass", "ir_unit": "module", "wall_ms": 0.5, "skipped": false}
          ]
        }
        """
    )

    loaded = audit.load_pipeline_report(report)

    assert audit.phase_map(loaded) == {"parse-ir": 1.25, "newpm-full": 3.5}
    assert audit.top_passes(loaded, limit=2) == [
        {"name": "SlowPass", "ir_unit": "module", "wall_ms": 2.0},
        {"name": "FastPass", "ir_unit": "module", "wall_ms": 0.5},
    ]


def test_load_pipeline_report_rejects_wrong_schema(tmp_path):
    audit = load_audit_module()
    report = tmp_path / "report.json"
    report.write_text('{"schema_version": 2, "phases": [], "passes": []}')

    with pytest.raises(audit.AuditError, match="unsupported pipeline report schema"):
        audit.load_pipeline_report(report)


def test_parse_opt_pass_inventory_groups_sections():
    audit = load_audit_module()
    inventory = audit.parse_opt_pass_inventory(
        """
Module passes:
  always-inline
  attributor
Function passes:
  instcombine
Module passes with params:
  global-merge<max-offset=N>
        """
    )

    assert inventory["module_passes"] == ["always-inline", "attributor"]
    assert inventory["function_passes"] == ["instcombine"]
    assert inventory["module_passes_with_params"] == ["global-merge<max-offset=N>"]


def test_build_opportunities_uses_fixture_evidence():
    audit = load_audit_module()
    fixtures = [
        {
            "label": "simple",
            "legacy": {
                "phases": {"parse-ir": 1.0, "pre-bpl": 1.0, "bpl-emission": 8.0},
            },
            "newpm": {
                "report": {"passes": [{"name": "BplFilePrinterNewPM"} for _ in range(4)]},
            },
        }
    ]

    opportunities = audit.build_opportunities(fixtures, {"module_passes": ["attributor"]})
    by_id = {opportunity["id"]: opportunity for opportunity in opportunities}

    assert "bpl-output-streaming" in by_id
    assert "80.0%" in by_id["bpl-output-streaming"]["evidence"]
    assert by_id["llvm-attributor-candidates"]["evidence"] == (
        "Local opt pass inventory includes Attributor passes."
    )

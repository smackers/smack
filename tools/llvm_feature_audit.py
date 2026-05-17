#!/usr/bin/env python3
"""Generate a report-only LLVM modernization audit for SMACK.

The probe intentionally avoids budgets: timing values are evidence for humans,
not pass/fail thresholds. Missing tools, broken llvm2bpl invocations, and
malformed pipeline reports still fail because they make the audit unusable.
"""

from __future__ import annotations

import argparse
import json
import shutil
import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import Any

SCHEMA_VERSION = 1

LLVM_DOCS = {
    "llvm_22_release_notes": "https://releases.llvm.org/22.1.0/docs/ReleaseNotes.html",
    "new_pass_manager": "https://releases.llvm.org/22.1.0/docs/NewPassManager.html",
    "opt_command": "https://releases.llvm.org/22.1.0/docs/CommandGuide/opt.html",
    "standard_instrumentations": "https://llvm.org/doxygen/classllvm_1_1StandardInstrumentations.html",
    "optimization_remarks": "https://llvm.org/docs/Remarks.html",
}


@dataclass(frozen=True)
class Fixture:
    label: str
    source: Path
    entry_point: str = "main"


FIXTURES = (
    Fixture("simple", Path("test/c/basic/simple.c")),
    Fixture("list", Path("test/c/basic/list.c")),
    Fixture("func_ptr", Path("test/c/data/func_ptr.c")),
)


class AuditError(RuntimeError):
    """Raised when audit evidence cannot be produced reliably."""


def _repo_root() -> Path:
    return Path(__file__).resolve().parents[1]


def _tool_candidates(name: str) -> list[Path]:
    return [
        Path(name),
        Path("/usr/lib/llvm-22/bin") / name,
    ]


def resolve_tool(value: str | None, name: str, *, base: Path | None = None) -> Path:
    if value:
        candidate = Path(value)
        candidates = [candidate]
        if base is not None and not candidate.is_absolute():
            candidates.insert(0, base / candidate)
    else:
        candidates = _tool_candidates(name)
    for candidate in candidates:
        if candidate.exists():
            return candidate.resolve()
    if value is None:
        found = shutil.which(name)
        if found:
            return Path(found).resolve()
    detail = value or name
    raise AuditError(f"required tool not found: {detail}")


def run_command(
    args: list[str],
    *,
    cwd: Path,
    timeout: int = 120,
) -> subprocess.CompletedProcess[str]:
    try:
        completed = subprocess.run(
            args,
            cwd=cwd,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            check=False,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired as exc:
        output = exc.stdout or ""
        if isinstance(output, bytes):
            output = output.decode(errors="replace")
        raise AuditError(f"command timed out after {timeout}s: {' '.join(args)}\n{output}") from exc

    if completed.returncode != 0:
        raise AuditError(
            "command failed with exit code "
            f"{completed.returncode}: {' '.join(args)}\n{completed.stdout}"
        )
    return completed


def _require_number(value: Any, field: str) -> float:
    if not isinstance(value, (int, float)):
        raise AuditError(f"expected numeric {field}, got {type(value).__name__}")
    return float(value)


def load_pipeline_report(path: Path) -> dict[str, Any]:
    try:
        data = json.loads(path.read_text())
    except json.JSONDecodeError as exc:
        raise AuditError(f"malformed JSON report: {path}") from exc

    if data.get("schema_version") != SCHEMA_VERSION:
        raise AuditError(f"unsupported pipeline report schema in {path}")

    phases = data.get("phases")
    if not isinstance(phases, list):
        raise AuditError(f"pipeline report missing phase list: {path}")
    for index, phase in enumerate(phases):
        if not isinstance(phase, dict) or not isinstance(phase.get("name"), str):
            raise AuditError(f"invalid phase at index {index}: {path}")
        _require_number(phase.get("wall_ms"), f"phases[{index}].wall_ms")

    passes = data.get("passes")
    if not isinstance(passes, list):
        raise AuditError(f"pipeline report missing pass list: {path}")
    for index, pass_timing in enumerate(passes):
        if not isinstance(pass_timing, dict) or not isinstance(pass_timing.get("name"), str):
            raise AuditError(f"invalid pass at index {index}: {path}")
        if not isinstance(pass_timing.get("ir_unit"), str):
            raise AuditError(f"invalid pass IR unit at index {index}: {path}")
        _require_number(pass_timing.get("wall_ms"), f"passes[{index}].wall_ms")
        if not isinstance(pass_timing.get("skipped"), bool):
            raise AuditError(f"invalid skipped flag at pass index {index}: {path}")

    return data


def phase_map(report: dict[str, Any]) -> dict[str, float]:
    return {phase["name"]: float(phase["wall_ms"]) for phase in report["phases"]}


def top_passes(report: dict[str, Any], limit: int = 10) -> list[dict[str, Any]]:
    passes = [pass_timing for pass_timing in report["passes"] if not pass_timing["skipped"]]
    passes.sort(key=lambda item: float(item["wall_ms"]), reverse=True)
    return [
        {
            "name": pass_timing["name"],
            "ir_unit": pass_timing["ir_unit"],
            "wall_ms": float(pass_timing["wall_ms"]),
        }
        for pass_timing in passes[:limit]
    ]


def parse_opt_pass_inventory(text: str) -> dict[str, list[str]]:
    inventory: dict[str, list[str]] = {}
    current: str | None = None
    for raw_line in text.splitlines():
        line = raw_line.rstrip()
        if not line:
            continue
        if not raw_line.startswith(" ") and line.endswith(":"):
            current = line[:-1].lower().replace(" ", "_")
            inventory[current] = []
            continue
        if current is not None and raw_line.startswith("  "):
            inventory[current].append(line.strip())
    return inventory


def _compile_fixture(
    *,
    fixture: Fixture,
    repo_root: Path,
    out_dir: Path,
    clang: Path,
    llvm_link: Path,
    runtime_bc: Path,
) -> Path:
    source = repo_root / fixture.source
    if not source.exists():
        raise AuditError(f"fixture source not found: {source}")

    bc = out_dir / f"{fixture.label}.bc"
    linked = out_dir / f"{fixture.label}-linked.bc"
    include_dir = repo_root / "share" / "smack" / "include"
    run_command(
        [
            str(clang),
            "-O0",
            "-g",
            "-emit-llvm",
            "-c",
            f"-I{include_dir}",
            str(source),
            "-o",
            str(bc),
        ],
        cwd=repo_root,
    )
    run_command(
        [str(llvm_link), str(bc), str(runtime_bc), "-o", str(linked)],
        cwd=repo_root,
    )
    return linked


def _compile_runtime(*, repo_root: Path, out_dir: Path, clang: Path) -> Path:
    runtime_bc = out_dir / "smack-runtime.bc"
    include_dir = repo_root / "share" / "smack" / "include"
    runtime_source = repo_root / "share" / "smack" / "lib" / "smack.c"
    run_command(
        [
            str(clang),
            "-O0",
            "-g",
            "-emit-llvm",
            "-c",
            f"-I{include_dir}",
            str(runtime_source),
            "-o",
            str(runtime_bc),
        ],
        cwd=repo_root,
    )
    return runtime_bc


def _run_llvm2bpl(
    *,
    llvm2bpl: Path,
    linked_bc: Path,
    fixture: Fixture,
    pipeline: str,
    repo_root: Path,
    out_dir: Path,
) -> dict[str, Any]:
    report_path = out_dir / f"{fixture.label}.{pipeline}.json"
    bpl_path = out_dir / f"{fixture.label}.{pipeline}.bpl"
    run_command(
        [
            str(llvm2bpl),
            f"--entry-points={fixture.entry_point}",
            f"--bpl={bpl_path}",
            "-smack-memory-partitioner=sea-dsa",
            f"--smack-pipeline-report={report_path}",
            str(linked_bc),
        ],
        cwd=repo_root,
    )
    report = load_pipeline_report(report_path)
    return {
        "report": report,
        "report_path": str(report_path),
        "bpl_path": str(bpl_path),
        "phases": phase_map(report),
        "top_passes": top_passes(report),
    }


def _phase_dominance_evidence(fixtures: list[dict[str, Any]]) -> str:
    ratios = []
    for fixture in fixtures:
        legacy = fixture["legacy"]
        phases = legacy["phases"]
        total = sum(phases.values())
        if total > 0 and "bpl-emission" in phases:
            ratios.append(phases["bpl-emission"] / total)
    if not ratios:
        return "Legacy report did not include bpl-emission phase data."
    return (
        "Legacy bpl-emission accounted for "
        f"{max(ratios) * 100:.1f}% of observed translator time in the hottest fixture."
    )


def build_opportunities(
    fixtures: list[dict[str, Any]],
    pass_inventory: dict[str, list[str]],
) -> list[dict[str, str]]:
    module_passes = pass_inventory.get("module_passes", [])
    has_attributor = "attributor" in module_passes or "attributor-light" in module_passes
    newpm_pass_counts = [
        len(fixture["newpm"]["report"]["passes"])
        for fixture in fixtures
        if fixture.get("newpm") is not None
    ]
    pass_count_evidence = (
        f"NewPM probe recorded up to {max(newpm_pass_counts)} pass events."
        if newpm_pass_counts
        else "NewPM probe was not available in this run."
    )

    return [
        {
            "id": "llvm-standard-instrumentations",
            "area": "observability",
            "impact": "medium",
            "risk": "low",
            "title": "Compare custom timing callbacks with LLVM StandardInstrumentations",
            "evidence": pass_count_evidence,
            "next_action": (
                "Prototype StandardInstrumentations or TimeProfilingPassesHandler behind the "
                "existing report flag and compare output usefulness."
            ),
        },
        {
            "id": "newpm-analysis-preservation",
            "area": "newpm",
            "impact": "medium",
            "risk": "medium",
            "title": "Audit PreservedAnalyses precision and pass grouping",
            "evidence": (
                "Several SMACK NewPM passes conservatively invalidate all analyses when changed; "
                "the probe can now show repeated adaptor and analysis costs."
            ),
            "next_action": (
                "Review each NewPM sibling for precise preservation of DominatorTree, LoopInfo, "
                "and module analyses before changing ordering."
            ),
        },
        {
            "id": "bpl-output-streaming",
            "area": "efficiency",
            "impact": "high",
            "risk": "medium",
            "title": "Stream Boogie output instead of staging full text in std::ostringstream",
            "evidence": _phase_dominance_evidence(fixtures),
            "next_action": (
                "Add an ostream/raw_ostream bridge or direct raw_ostream printer path, then "
                "compare BPL byte-for-byte output and timing reports."
            ),
        },
        {
            "id": "llvm22-ptrtoaddr",
            "area": "llvm-ir",
            "impact": "medium",
            "risk": "high",
            "title": "Evaluate LLVM 22 ptrtoaddr effects on SMACK pointer/provenance modeling",
            "evidence": (
                "LLVM 22 introduced ptrtoaddr; SMACK still has explicit ptrtoint cleanup and "
                "legacy sea-dsa pointer reasoning bridges."
            ),
            "next_action": (
                "Add focused IR fixtures containing ptrtoaddr before changing lowering or "
                "RemovePtrToInt assumptions."
            ),
        },
        {
            "id": "llvm-attributor-candidates",
            "area": "llvm-features",
            "impact": "low",
            "risk": "medium",
            "title": "Screen LLVM Attributor and inference passes for verifier-safe simplification",
            "evidence": (
                "Local opt pass inventory includes Attributor passes."
                if has_attributor
                else "Local opt inventory did not expose Attributor passes."
            ),
            "next_action": (
                "Run candidate passes only in exploratory builds and diff emitted BPL before "
                "considering them for the production pipeline."
            ),
        },
    ]


def _format_phase_table(fixtures: list[dict[str, Any]]) -> str:
    rows = ["| Fixture | Pipeline | Phases |", "| --- | --- | --- |"]
    for fixture in fixtures:
        for pipeline in ("legacy", "newpm"):
            result = fixture.get(pipeline)
            if result is None:
                continue
            phases = ", ".join(f"{name}={value:.2f}ms" for name, value in result["phases"].items())
            rows.append(f"| {fixture['label']} | {pipeline} | {phases} |")
    return "\n".join(rows)


def _format_opportunity_table(opportunities: list[dict[str, str]]) -> str:
    rows = ["| ID | Area | Impact | Risk | Next action |", "| --- | --- | --- | --- | --- |"]
    for opportunity in opportunities:
        rows.append("| {id} | {area} | {impact} | {risk} | {next_action} |".format(**opportunity))
    return "\n".join(rows)


def render_markdown(audit: dict[str, Any]) -> str:
    llvm = audit["llvm"]
    docs = audit["references"]
    return (
        "\n\n".join(
            [
                "# LLVM Modernization Audit",
                (
                    "Report-only audit generated from `llvm2bpl --smack-pipeline-report` "
                    "and local LLVM tooling. Timings are diagnostic and are not budgets."
                ),
                "## LLVM Baseline\n\n"
                f"- Configured LLVM: `{llvm['configured_version']}`\n"
                f"- Detected `llvm-config`: `{llvm['detected_version']}`\n"
                f"- `opt --print-passes` sections: `{len(audit['available_passes'])}`",
                "## Fixture Timings\n\n" + _format_phase_table(audit["fixtures"]),
                "## Opportunities\n\n" + _format_opportunity_table(audit["opportunities"]),
                "## References\n\n" + "\n".join(f"- [{name}]({url})" for name, url in docs.items()),
            ]
        )
        + "\n"
    )


def _configured_llvm_version(repo_root: Path) -> str:
    versions = repo_root / "bin" / "versions"
    for line in versions.read_text().splitlines():
        if line.startswith("LLVM_FULL_VERSION="):
            return line.split("=", 1)[1].strip().strip('"')
    return "unknown"


def collect_audit(args: argparse.Namespace) -> dict[str, Any]:
    repo_root = args.repo_root.resolve()
    out_dir = args.out_dir.resolve()
    out_dir.mkdir(parents=True, exist_ok=True)
    work_dir = out_dir / "work"
    work_dir.mkdir(parents=True, exist_ok=True)

    legacy_llvm2bpl = resolve_tool(args.legacy_llvm2bpl, "llvm2bpl", base=repo_root)
    newpm_llvm2bpl = (
        resolve_tool(args.newpm_llvm2bpl, "llvm2bpl", base=repo_root)
        if args.newpm_llvm2bpl
        else None
    )
    clang = resolve_tool(args.clang, "clang-22", base=repo_root)
    llvm_link = resolve_tool(args.llvm_link, "llvm-link-22", base=repo_root)
    opt = resolve_tool(args.opt, "opt-22", base=repo_root)
    llvm_config = resolve_tool(args.llvm_config, "llvm-config-22", base=repo_root)

    opt_output = run_command([str(opt), "--print-passes"], cwd=repo_root)
    pass_inventory = parse_opt_pass_inventory(opt_output.stdout)
    detected_version = run_command([str(llvm_config), "--version"], cwd=repo_root).stdout.strip()

    runtime_bc = _compile_runtime(repo_root=repo_root, out_dir=work_dir, clang=clang)

    fixture_results = []
    for fixture in FIXTURES:
        linked_bc = _compile_fixture(
            fixture=fixture,
            repo_root=repo_root,
            out_dir=work_dir,
            clang=clang,
            llvm_link=llvm_link,
            runtime_bc=runtime_bc,
        )
        result: dict[str, Any] = {
            "label": fixture.label,
            "source": str(fixture.source),
            "entry_point": fixture.entry_point,
            "legacy": _run_llvm2bpl(
                llvm2bpl=legacy_llvm2bpl,
                linked_bc=linked_bc,
                fixture=fixture,
                pipeline="legacy",
                repo_root=repo_root,
                out_dir=out_dir,
            ),
            "newpm": None,
        }
        if newpm_llvm2bpl is not None:
            result["newpm"] = _run_llvm2bpl(
                llvm2bpl=newpm_llvm2bpl,
                linked_bc=linked_bc,
                fixture=fixture,
                pipeline="newpm",
                repo_root=repo_root,
                out_dir=out_dir,
            )
        fixture_results.append(result)

    audit = {
        "schema_version": SCHEMA_VERSION,
        "llvm": {
            "configured_version": _configured_llvm_version(repo_root),
            "detected_version": detected_version,
            "legacy_llvm2bpl": str(legacy_llvm2bpl),
            "newpm_llvm2bpl": str(newpm_llvm2bpl) if newpm_llvm2bpl else None,
            "clang": str(clang),
            "llvm_link": str(llvm_link),
            "opt": str(opt),
        },
        "fixtures": fixture_results,
        "available_passes": pass_inventory,
        "opportunities": build_opportunities(fixture_results, pass_inventory),
        "references": LLVM_DOCS,
    }
    return audit


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--legacy-llvm2bpl", required=True)
    parser.add_argument("--newpm-llvm2bpl")
    parser.add_argument("--clang")
    parser.add_argument("--llvm-link")
    parser.add_argument("--opt")
    parser.add_argument("--llvm-config")
    parser.add_argument("--repo-root", type=Path, default=_repo_root())
    parser.add_argument("--out-dir", type=Path, required=True)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    try:
        audit = collect_audit(args)
    except AuditError as exc:
        print(f"llvm_feature_audit: {exc}")
        return 1

    audit_json = args.out_dir / "audit.json"
    audit_md = args.out_dir / "audit.md"
    audit_json.write_text(json.dumps(audit, indent=2, sort_keys=True) + "\n")
    audit_md.write_text(render_markdown(audit))
    print(f"wrote {audit_json}")
    print(f"wrote {audit_md}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

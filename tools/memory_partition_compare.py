#!/usr/bin/env python3
"""Compare SMACK memory partitioning candidates with report evidence.

The ranking is map-count-oriented: successful candidates with more emitted
Boogie memory maps rank first, then region/type counts and fallback diagnostics
break ties. Failures are recorded per candidate instead of aborting the whole
comparison.
"""

from __future__ import annotations

import argparse
import json
import shlex
import shutil
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any

SCHEMA_VERSION = 1
SUPPORTED_MEMORY_REPORT_SCHEMAS = {1, 2}

REGION_KEYS = (
    "singleton",
    "allocated",
    "bytewise",
    "incomplete",
    "complicated",
    "collapsed",
    "typed",
    "untyped",
)

IMPRECISE_REGION_KEYS = ("bytewise", "incomplete", "complicated", "collapsed", "untyped")

DEFAULT_CANDIDATES = (
    "sea-dsa-ci=-sea-dsa=ci -smack-memory-partitioner=sea-dsa",
    "sea-dsa-bu=-sea-dsa=bu -smack-memory-partitioner=sea-dsa",
    "sea-dsa-butd-cs=-sea-dsa=butd-cs -smack-memory-partitioner=sea-dsa",
    "sea-dsa-cs=-sea-dsa=cs -smack-memory-partitioner=sea-dsa",
    "sea-dsa-flat=-sea-dsa=flat -smack-memory-partitioner=sea-dsa",
    (
        "teadsa-butd-cs-type-aware=-sea-dsa=butd-cs -sea-dsa-type-aware "
        "-smack-memory-partitioner=sea-dsa"
    ),
    "cell-refined-ci=-sea-dsa=ci -smack-memory-partitioner=cell-refined",
    "cell-refined-butd-cs=-sea-dsa=butd-cs -smack-memory-partitioner=cell-refined",
    "aa-refined-bu=-sea-dsa=bu -smack-memory-partitioner=aa-refined",
    (
        "aa-refined-teadsa=-sea-dsa=butd-cs -sea-dsa-type-aware "
        "-smack-memory-partitioner=aa-refined"
    ),
)

DEFAULT_FIXTURES = (
    "simple=test/c/basic/simple.c:main",
    "list=test/c/basic/list.c:main",
    "func_ptr=test/c/data/func_ptr.c:main",
    "struct_alias=test/c/data/struct_alias.c:main",
)

DEFAULT_EXTERNAL_PROBES = (
    "svf=wpa,svf-ex",
    "cclyzerpp=cclyzer++,cclyzer",
    "phasar=phasar-llvm,phasar",
    "phoenix=phoenix",
)

SVF_MEM_PAR_MODES = ("distinct", "intra-disjoint", "inter-disjoint")


@dataclass(frozen=True)
class Candidate:
    label: str
    flags: tuple[str, ...]


@dataclass(frozen=True)
class Fixture:
    label: str
    source: Path
    entry_point: str = "main"
    kind: str = "source"
    link_runtime: bool = True


@dataclass(frozen=True)
class ExternalProbe:
    label: str
    tools: tuple[str, ...]


class CompareError(RuntimeError):
    """Raised when comparison evidence cannot be produced reliably."""


def _repo_root() -> Path:
    return Path(__file__).resolve().parents[1]


def resolve_tool(value: str | None, name: str, *, repo_root: Path) -> Path:
    candidates: list[Path]
    if value:
        path = Path(value)
        candidates = [path]
        if not path.is_absolute():
            candidates.insert(0, repo_root / path)
    else:
        candidates = [
            repo_root / "build-llvm22c" / name,
            Path(name),
            Path("/usr/lib/llvm-22/bin") / name,
        ]

    for candidate in candidates:
        if candidate.exists():
            return candidate.resolve()

    if value is None:
        found = shutil.which(name)
        if found:
            return Path(found).resolve()

    raise CompareError(f"required tool not found: {value or name}")


def run_command(
    args: list[str],
    *,
    cwd: Path,
    timeout: int,
    check: bool = True,
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
        completed = subprocess.CompletedProcess(args, 124, output)

    if check and completed.returncode != 0:
        raise CompareError(
            "command failed with exit code "
            f"{completed.returncode}: {' '.join(args)}\n{completed.stdout}"
        )
    return completed


def parse_candidate(spec: str) -> Candidate:
    if "=" not in spec:
        raise CompareError(f"candidate must use NAME=FLAGS syntax: {spec}")
    label, flags = spec.split("=", 1)
    label = label.strip()
    if not label:
        raise CompareError(f"candidate label is empty: {spec}")
    return Candidate(label=label, flags=tuple(shlex.split(flags)))


def parse_fixture(spec: str) -> Fixture:
    if "=" not in spec:
        raise CompareError(f"fixture must use NAME=PATH[:ENTRY] syntax: {spec}")
    label, rest = spec.split("=", 1)
    label = label.strip()
    if not label:
        raise CompareError(f"fixture label is empty: {spec}")

    path_text, separator, entry_point = rest.rpartition(":")
    if separator:
        return Fixture(label=label, source=Path(path_text), entry_point=entry_point or "main")
    return Fixture(label=label, source=Path(rest), entry_point="main")


def parse_external_probe(spec: str) -> ExternalProbe:
    if "=" not in spec:
        raise CompareError(f"external candidate must use NAME=TOOL[,TOOL] syntax: {spec}")
    label, tools_text = spec.split("=", 1)
    label = label.strip()
    tools = tuple(tool.strip() for tool in tools_text.split(",") if tool.strip())
    if not label:
        raise CompareError(f"external candidate label is empty: {spec}")
    if not tools:
        raise CompareError(f"external candidate tools are empty: {spec}")
    return ExternalProbe(label=label, tools=tools)


def resolve_external_probe_tool(probe: ExternalProbe, *, repo_root: Path) -> Path | None:
    for tool in probe.tools:
        candidate = Path(tool)
        if not candidate.is_absolute():
            repo_candidate = repo_root / candidate
            if repo_candidate.exists():
                return repo_candidate.resolve()
        elif candidate.exists():
            return candidate.resolve()
        found = shutil.which(tool)
        if found:
            return Path(found).resolve()
    return None


def probe_external_candidate(probe: ExternalProbe, *, repo_root: Path) -> dict[str, Any]:
    tool = resolve_external_probe_tool(probe, repo_root=repo_root)
    if tool and probe.label.startswith("svf"):
        return {
            "candidate": probe.label,
            "status": "available",
            "tool": str(tool),
            "reason": (
                "SVF MemorySSA sidecar metrics can be collected; these are "
                "not yet sound SMACK memory maps for the main ranking"
            ),
        }
    if tool:
        return {
            "candidate": probe.label,
            "status": "skipped",
            "tool": str(tool),
            "reason": (
                "external analyzer found, but no adapter currently emits "
                "sound SMACK memory maps or comparable partition metrics"
            ),
        }
    return {
        "candidate": probe.label,
        "status": "skipped",
        "tool": None,
        "reason": f"none of the configured tools were found: {', '.join(probe.tools)}",
    }


def parse_bc_fixture(spec: str, *, link_runtime: bool = True) -> Fixture:
    fixture = parse_fixture(spec)
    return Fixture(
        label=fixture.label,
        source=fixture.source,
        entry_point=fixture.entry_point,
        kind="bitcode",
        link_runtime=link_runtime,
    )


def resolve_repo_path(path: Path, *, repo_root: Path) -> Path:
    if path.is_absolute():
        return path
    return repo_root / path


def _require_nonnegative_int(value: Any, field: str) -> int:
    if not isinstance(value, int) or value < 0:
        raise CompareError(f"expected nonnegative integer {field}, got {value!r}")
    return value


def load_memory_report(path: Path) -> dict[str, Any]:
    try:
        data = json.loads(path.read_text())
    except json.JSONDecodeError as exc:
        raise CompareError(f"malformed JSON report: {path}") from exc

    if data.get("schema_version") not in SUPPORTED_MEMORY_REPORT_SCHEMAS:
        raise CompareError(f"unsupported memory report schema in {path}")
    for field in ("llvm_version", "pipeline", "input", "partitioner", "dsa_mode"):
        if not isinstance(data.get(field), str):
            raise CompareError(f"memory report missing string field {field}: {path}")
    for field in ("region_count", "memory_access_count", "merge_count", "late_region_count"):
        _require_nonnegative_int(data.get(field), field)

    regions = data.get("regions")
    if not isinstance(regions, dict):
        raise CompareError(f"memory report missing regions object: {path}")
    for key in REGION_KEYS:
        _require_nonnegative_int(regions.get(key), f"regions.{key}")

    reasons = data.get("fallback_reasons")
    if not isinstance(reasons, list):
        raise CompareError(f"memory report missing fallback_reasons list: {path}")
    for index, reason in enumerate(reasons):
        if not isinstance(reason, dict) or not isinstance(reason.get("name"), str):
            raise CompareError(f"invalid fallback reason at index {index}: {path}")
        _require_nonnegative_int(reason.get("count"), f"fallback_reasons[{index}].count")
    return data


def fallback_total(report: dict[str, Any]) -> int:
    return sum(int(reason["count"]) for reason in report["fallback_reasons"])


def imprecise_region_count(report: dict[str, Any]) -> int:
    regions = report["regions"]
    return sum(int(regions[key]) for key in IMPRECISE_REGION_KEYS)


def count_boogie_memory_maps(path: Path) -> int:
    try:
        return sum(1 for line in path.read_text().splitlines() if line.startswith("var $M."))
    except OSError as exc:
        raise CompareError(f"could not read Boogie output for memory maps: {path}") from exc


def precision_metrics(report: dict[str, Any], *, memory_map_count: int = 0) -> dict[str, int]:
    regions = report["regions"]
    return {
        "fallback_total": fallback_total(report),
        "imprecise_region_count": imprecise_region_count(report),
        "memory_map_count": memory_map_count,
        "region_count": int(report["region_count"]),
        "typed_region_count": int(regions["typed"]),
        "singleton_count": int(regions["singleton"]),
        "merge_count": int(report["merge_count"]),
        "late_region_count": int(report["late_region_count"]),
    }


def _compile_runtime(*, repo_root: Path, out_dir: Path, clang: Path, timeout: int) -> Path:
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
        timeout=timeout,
    )
    return runtime_bc


def _compile_fixture(
    *,
    fixture: Fixture,
    repo_root: Path,
    out_dir: Path,
    clang: Path,
    llvm_link: Path,
    runtime_bc: Path,
    timeout: int,
) -> Path:
    source = resolve_repo_path(fixture.source, repo_root=repo_root)
    if not source.exists():
        raise CompareError(f"fixture source not found: {source}")

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
        timeout=timeout,
    )
    run_command(
        [str(llvm_link), str(bc), str(runtime_bc), "-o", str(linked)],
        cwd=repo_root,
        timeout=timeout,
    )
    return linked


def _prepare_bitcode_fixture(
    *,
    fixture: Fixture,
    repo_root: Path,
    out_dir: Path,
    llvm_link: Path,
    runtime_bc: Path | None,
    timeout: int,
) -> Path:
    source = resolve_repo_path(fixture.source, repo_root=repo_root)
    if not source.exists():
        raise CompareError(f"bitcode fixture not found: {source}")

    if not fixture.link_runtime:
        return source

    if runtime_bc is None:
        raise CompareError(f"runtime bitcode required for bitcode fixture: {fixture.label}")

    linked = out_dir / f"{fixture.label}-linked.bc"
    run_command(
        [str(llvm_link), str(source), str(runtime_bc), "-o", str(linked)],
        cwd=repo_root,
        timeout=timeout,
    )
    return linked


def _prepare_fixture_bitcode(
    *,
    fixture: Fixture,
    repo_root: Path,
    out_dir: Path,
    clang: Path,
    llvm_link: Path,
    runtime_bc: Path | None,
    timeout: int,
) -> Path:
    if fixture.kind == "source":
        if runtime_bc is None:
            raise CompareError(f"runtime bitcode required for source fixture: {fixture.label}")
        return _compile_fixture(
            fixture=fixture,
            repo_root=repo_root,
            out_dir=out_dir,
            clang=clang,
            llvm_link=llvm_link,
            runtime_bc=runtime_bc,
            timeout=timeout,
        )
    if fixture.kind == "bitcode":
        return _prepare_bitcode_fixture(
            fixture=fixture,
            repo_root=repo_root,
            out_dir=out_dir,
            llvm_link=llvm_link,
            runtime_bc=runtime_bc,
            timeout=timeout,
        )
    raise CompareError(f"unsupported fixture kind for {fixture.label}: {fixture.kind}")


def _error_tail(output: str, *, limit: int = 20) -> str:
    return "\n".join(output.splitlines()[-limit:])


def _extract_stat_block(output: str, title: str) -> str:
    marker = f"*********{title}***************"
    start = output.find(marker)
    if start < 0:
        raise CompareError(f"SVF output missing statistics block: {title}")
    next_block = output.find("*********", start + len(marker))
    if next_block < 0:
        return output[start:]
    return output[start:next_block]


def _parse_stat_value(text: str) -> int | float:
    if "." in text:
        return float(text)
    return int(text)


def parse_svf_mssa_metrics(output: str) -> dict[str, int | float]:
    block = _extract_stat_block(output, "Memory SSA Statistics")
    raw: dict[str, int | float] = {}
    for line in block.splitlines():
        parts = line.split()
        if len(parts) != 2:
            continue
        key, value = parts
        try:
            raw[key] = _parse_stat_value(value)
        except ValueError:
            continue

    required = (
        "MemRegions",
        "AverageRegSize",
        "MaxRegSize",
        "LoadMuNode",
        "StoreChiNode",
        "MSSAPhi",
        "TotalMSSATime",
    )
    missing = [key for key in required if key not in raw]
    if missing:
        raise CompareError(f"SVF MemorySSA metrics missing fields: {', '.join(missing)}")

    return {
        "memory_region_count": int(raw["MemRegions"]),
        "average_region_size": float(raw["AverageRegSize"]),
        "max_region_size": int(raw["MaxRegSize"]),
        "load_mu_node_count": int(raw["LoadMuNode"]),
        "store_chi_node_count": int(raw["StoreChiNode"]),
        "mssa_phi_count": int(raw["MSSAPhi"]),
        "total_mssa_time": float(raw["TotalMSSATime"]),
    }


def infer_svf_extapi_path(tool: Path, override: Path | None) -> Path | None:
    candidates: list[Path] = []
    if override:
        candidates.append(override)
    candidates.extend(
        [
            tool.parent.parent / "lib" / "extapi.bc",
            tool.parent / "extapi.bc",
        ]
    )
    for candidate in candidates:
        if candidate.exists():
            return candidate.resolve()
    return None


def _run_svf_mssa_candidate(
    *,
    tool: Path,
    extapi: Path,
    linked_bc: Path,
    fixture: Fixture,
    probe: ExternalProbe,
    mem_par: str,
    repo_root: Path,
    timeout: int,
) -> dict[str, Any]:
    candidate_label = f"{probe.label}-andersen-{mem_par}"
    command = [
        str(tool),
        "-ander",
        "-svfg",
        f"-mem-par={mem_par}",
        f"-extapi={extapi}",
        str(linked_bc),
    ]
    start = time.monotonic()
    completed = run_command(command, cwd=repo_root, timeout=timeout, check=False)
    wall_ms = (time.monotonic() - start) * 1000.0
    base: dict[str, Any] = {
        "fixture": fixture.label,
        "candidate": candidate_label,
        "kind": "external-svf-mssa",
        "tool": str(tool),
        "flags": command[1:-1],
        "command": command,
        "returncode": completed.returncode,
        "wall_ms": wall_ms,
    }
    if completed.returncode != 0:
        base.update({"status": "failed", "error": _error_tail(completed.stdout)})
        return base
    try:
        metrics = parse_svf_mssa_metrics(completed.stdout)
    except CompareError as exc:
        base.update({"status": "failed", "error": str(exc)})
        return base
    base.update({"status": "ok", "metrics": metrics})
    return base


def _run_external_partition_candidates(
    *,
    linked_bc: Path,
    fixture: Fixture,
    external_probes: list[ExternalProbe],
    repo_root: Path,
    svf_extapi: Path | None,
    timeout: int,
) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    for probe in external_probes:
        if not probe.label.startswith("svf"):
            continue
        tool = resolve_external_probe_tool(probe, repo_root=repo_root)
        if tool is None:
            continue
        extapi = infer_svf_extapi_path(tool, svf_extapi)
        if extapi is None:
            records.append(
                {
                    "fixture": fixture.label,
                    "candidate": probe.label,
                    "kind": "external-svf-mssa",
                    "tool": str(tool),
                    "flags": [],
                    "command": [],
                    "returncode": 0,
                    "wall_ms": 0.0,
                    "status": "failed",
                    "error": "SVF extapi.bc not found; pass --svf-extapi",
                }
            )
            continue
        for mem_par in SVF_MEM_PAR_MODES:
            records.append(
                _run_svf_mssa_candidate(
                    tool=tool,
                    extapi=extapi,
                    linked_bc=linked_bc,
                    fixture=fixture,
                    probe=probe,
                    mem_par=mem_par,
                    repo_root=repo_root,
                    timeout=timeout,
                )
            )
    return records


def _run_candidate(
    *,
    llvm2bpl: Path,
    linked_bc: Path,
    fixture: Fixture,
    candidate: Candidate,
    repo_root: Path,
    out_dir: Path,
    timeout: int,
) -> dict[str, Any]:
    report_path = out_dir / f"{fixture.label}.{candidate.label}.memory.json"
    bpl_path = out_dir / f"{fixture.label}.{candidate.label}.bpl"
    command = [
        str(llvm2bpl),
        *candidate.flags,
        f"--entry-points={fixture.entry_point}",
        f"--bpl={bpl_path}",
        f"--smack-memory-partition-report={report_path}",
        str(linked_bc),
    ]

    start = time.monotonic()
    completed = run_command(command, cwd=repo_root, timeout=timeout, check=False)
    wall_ms = (time.monotonic() - start) * 1000.0
    base: dict[str, Any] = {
        "fixture": fixture.label,
        "candidate": candidate.label,
        "flags": list(candidate.flags),
        "command": command,
        "returncode": completed.returncode,
        "wall_ms": wall_ms,
        "report_path": str(report_path),
        "bpl_path": str(bpl_path),
    }
    if completed.returncode != 0:
        base.update({"status": "failed", "error": _error_tail(completed.stdout)})
        return base
    try:
        report = load_memory_report(report_path)
        memory_map_count = count_boogie_memory_maps(bpl_path)
    except CompareError as exc:
        base.update({"status": "failed", "error": str(exc)})
        return base

    base.update(
        {
            "status": "ok",
            "report": report,
            "metrics": precision_metrics(report, memory_map_count=memory_map_count),
        }
    )
    return base


def _svf_refined_label(mem_par: str) -> str:
    if mem_par == "intra-disjoint":
        return "svf-refined-bu"
    return f"svf-refined-bu-{mem_par}"


def _requires_generated_svf_refined_oracle(candidate: Candidate) -> bool:
    uses_svf_refined = any(
        flag == "-smack-memory-partitioner=svf-refined"
        or (
            flag == "-smack-memory-partitioner"
            and idx + 1 < len(candidate.flags)
            and candidate.flags[idx + 1] == "svf-refined"
        )
        for idx, flag in enumerate(candidate.flags)
    )
    has_oracle = any(
        flag == "-smack-memory-partition-oracle"
        or flag.startswith("-smack-memory-partition-oracle=")
        for flag in candidate.flags
    )
    return uses_svf_refined and not has_oracle


def _svf_native_label(mem_par: str) -> str:
    if mem_par == "intra-disjoint":
        return "svf-native"
    return f"svf-native-{mem_par}"


def _run_svf_refined_candidate(
    *,
    llvm2bpl: Path,
    linked_bc: Path,
    fixture: Fixture,
    svf_wpa: Path,
    svf_extapi: Path,
    mem_par: str,
    repo_root: Path,
    out_dir: Path,
    timeout: int,
) -> dict[str, Any]:
    candidate_label = _svf_refined_label(mem_par)
    kind = "integrated-svf-refined"
    pre_ll_path = out_dir / f"{fixture.label}.{candidate_label}.pre.ll"
    pre_report_path = out_dir / f"{fixture.label}.{candidate_label}.pre.pipeline.json"
    oracle_path = out_dir / f"{fixture.label}.{candidate_label}.oracle.json"
    adapter_path = repo_root / "tools" / "svf_memory_partition_adapter.py"
    start = time.monotonic()

    preprocess_command = [
        str(llvm2bpl),
        f"--entry-points={fixture.entry_point}",
        "-no-memory-splitting",
        f"--ll={pre_ll_path}",
        f"--smack-pipeline-report={pre_report_path}",
        str(linked_bc),
    ]
    completed = run_command(preprocess_command, cwd=repo_root, timeout=timeout, check=False)
    if completed.returncode != 0:
        return {
            "fixture": fixture.label,
            "candidate": candidate_label,
            "kind": kind,
            "stage": "pre-bpl",
            "flags": [],
            "command": preprocess_command,
            "returncode": completed.returncode,
            "wall_ms": (time.monotonic() - start) * 1000.0,
            "pre_ll_path": str(pre_ll_path),
            "oracle_path": str(oracle_path),
            "status": "failed",
            "error": _error_tail(completed.stdout),
        }

    adapter_command = [
        sys.executable,
        str(adapter_path),
        "--bc",
        str(pre_ll_path),
        "--out",
        str(oracle_path),
        "--svf-wpa",
        str(svf_wpa),
        "--svf-extapi",
        str(svf_extapi),
        "--mem-par",
        mem_par,
        "--timeout",
        str(timeout),
    ]
    completed = run_command(adapter_command, cwd=repo_root, timeout=timeout, check=False)
    if completed.returncode != 0:
        return {
            "fixture": fixture.label,
            "candidate": candidate_label,
            "kind": kind,
            "stage": "oracle",
            "flags": [],
            "command": adapter_command,
            "returncode": completed.returncode,
            "wall_ms": (time.monotonic() - start) * 1000.0,
            "pre_ll_path": str(pre_ll_path),
            "oracle_path": str(oracle_path),
            "status": "failed",
            "error": _error_tail(completed.stdout),
        }

    flags = ["-sea-dsa=bu", "-smack-memory-partitioner=svf-refined"]
    flags.append(f"-smack-memory-partition-oracle={oracle_path}")
    candidate = Candidate(label=candidate_label, flags=tuple(flags))
    record = _run_candidate(
        llvm2bpl=llvm2bpl,
        linked_bc=linked_bc,
        fixture=fixture,
        candidate=candidate,
        repo_root=repo_root,
        out_dir=out_dir,
        timeout=timeout,
    )
    record["kind"] = kind
    record["stage"] = "bpl"
    record["pre_ll_path"] = str(pre_ll_path)
    record["oracle_path"] = str(oracle_path)
    record["wall_ms"] = (time.monotonic() - start) * 1000.0
    return record


def _run_svf_native_candidate(
    *,
    llvm2bpl: Path,
    linked_bc: Path,
    fixture: Fixture,
    svf_extapi: Path | None,
    mem_par: str,
    repo_root: Path,
    out_dir: Path,
    timeout: int,
) -> dict[str, Any]:
    candidate_label = _svf_native_label(mem_par)
    flags = ["-smack-memory-partitioner=svf-native", f"-smack-svf-mem-par={mem_par}"]
    if svf_extapi is not None:
        flags.append(f"-smack-svf-extapi={svf_extapi}")
    record = _run_candidate(
        llvm2bpl=llvm2bpl,
        linked_bc=linked_bc,
        fixture=fixture,
        candidate=Candidate(label=candidate_label, flags=tuple(flags)),
        repo_root=repo_root,
        out_dir=out_dir,
        timeout=timeout,
    )
    record["kind"] = "integrated-svf-native"
    record["stage"] = "bpl"
    return record


def rank_candidates(records: list[dict[str, Any]]) -> list[dict[str, Any]]:
    grouped: dict[str, list[dict[str, Any]]] = {}
    for record in records:
        grouped.setdefault(str(record["candidate"]), []).append(record)

    ranking = []
    for candidate, candidate_records in grouped.items():
        failures = [record for record in candidate_records if record["status"] != "ok"]
        ok_records = [record for record in candidate_records if record["status"] == "ok"]
        aggregate = {
            "fallback_total": sum(record["metrics"]["fallback_total"] for record in ok_records),
            "imprecise_region_count": sum(
                record["metrics"]["imprecise_region_count"] for record in ok_records
            ),
            "memory_map_count": sum(record["metrics"]["memory_map_count"] for record in ok_records),
            "region_count": sum(record["metrics"]["region_count"] for record in ok_records),
            "typed_region_count": sum(
                record["metrics"]["typed_region_count"] for record in ok_records
            ),
            "singleton_count": sum(record["metrics"]["singleton_count"] for record in ok_records),
            "merge_count": sum(record["metrics"]["merge_count"] for record in ok_records),
            "late_region_count": sum(
                record["metrics"]["late_region_count"] for record in ok_records
            ),
            "wall_ms": sum(float(record["wall_ms"]) for record in candidate_records),
        }
        ranking.append(
            {
                "candidate": candidate,
                "status": "failed" if len(failures) == len(candidate_records) else "ok",
                "ok_count": len(ok_records),
                "failure_count": len(failures),
                "metrics": aggregate,
            }
        )

    ranking.sort(
        key=lambda item: (
            item["failure_count"],
            -item["metrics"]["memory_map_count"],
            -item["metrics"]["region_count"],
            -item["metrics"]["typed_region_count"],
            item["metrics"]["fallback_total"],
            item["metrics"]["imprecise_region_count"],
            item["metrics"]["merge_count"],
            item["metrics"]["wall_ms"],
            item["candidate"],
        )
    )
    for index, item in enumerate(ranking, start=1):
        item["rank"] = index
    return ranking


def rank_external_candidates(records: list[dict[str, Any]]) -> list[dict[str, Any]]:
    grouped: dict[str, list[dict[str, Any]]] = {}
    for record in records:
        grouped.setdefault(str(record["candidate"]), []).append(record)

    ranking = []
    for candidate, candidate_records in grouped.items():
        failures = [record for record in candidate_records if record["status"] != "ok"]
        ok_records = [record for record in candidate_records if record["status"] == "ok"]
        aggregate = {
            "memory_region_count": sum(
                record["metrics"]["memory_region_count"] for record in ok_records
            ),
            "average_region_size": sum(
                record["metrics"]["average_region_size"] for record in ok_records
            ),
            "max_region_size": max(
                (record["metrics"]["max_region_size"] for record in ok_records),
                default=0,
            ),
            "load_mu_node_count": sum(
                record["metrics"]["load_mu_node_count"] for record in ok_records
            ),
            "store_chi_node_count": sum(
                record["metrics"]["store_chi_node_count"] for record in ok_records
            ),
            "mssa_phi_count": sum(record["metrics"]["mssa_phi_count"] for record in ok_records),
            "total_mssa_time": sum(
                record["metrics"]["total_mssa_time"] for record in ok_records
            ),
            "wall_ms": sum(float(record["wall_ms"]) for record in candidate_records),
        }
        ranking.append(
            {
                "candidate": candidate,
                "status": "failed" if len(failures) == len(candidate_records) else "ok",
                "ok_count": len(ok_records),
                "failure_count": len(failures),
                "metrics": aggregate,
            }
        )

    ranking.sort(
        key=lambda item: (
            item["failure_count"],
            -item["ok_count"],
            -item["metrics"]["memory_region_count"],
            item["metrics"]["average_region_size"],
            item["metrics"]["max_region_size"],
            item["metrics"]["total_mssa_time"],
            item["metrics"]["wall_ms"],
            item["candidate"],
        )
    )
    for index, item in enumerate(ranking, start=1):
        item["rank"] = index
    return ranking


def build_summary(
    *,
    repo_root: Path,
    llvm2bpl: Path,
    clang: Path,
    llvm_link: Path,
    fixtures: list[Fixture],
    candidates: list[Candidate],
    records: list[dict[str, Any]],
    external_probes: list[ExternalProbe],
    external_records: list[dict[str, Any]],
) -> dict[str, Any]:
    ranking = rank_candidates(records)
    return {
        "schema_version": SCHEMA_VERSION,
        "repo_root": str(repo_root),
        "tools": {
            "llvm2bpl": str(llvm2bpl),
            "clang": str(clang),
            "llvm_link": str(llvm_link),
        },
        "ranking_rule": (
            "fewer failed fixtures, more Boogie memory maps, more regions, "
            "more typed regions, fewer fallback/imprecise regions, fewer merges, "
            "then less wall time"
        ),
        "external_ranking_rule": (
            "SVF sidecar only: fewer failed fixtures, more SVF MemorySSA regions, "
            "smaller average/max region size, then less analysis time"
        ),
        "fixtures": [
            {
                "label": fixture.label,
                "kind": fixture.kind,
                "source": str(fixture.source),
                "entry_point": fixture.entry_point,
                "link_runtime": fixture.link_runtime,
            }
            for fixture in fixtures
        ],
        "candidates": [
            {"label": candidate.label, "flags": list(candidate.flags)} for candidate in candidates
        ],
        "external_candidates": [
            probe_external_candidate(probe, repo_root=repo_root) for probe in external_probes
        ],
        "external_ranking": rank_external_candidates(external_records),
        "external_records": external_records,
        "ranking": ranking,
        "records": records,
    }


def write_markdown(summary: dict[str, Any], path: Path) -> None:
    lines = [
        "# SMACK Memory Partitioning Comparison",
        "",
        f"Ranking rule: {summary['ranking_rule']}.",
        "",
        "## Ranking",
        "",
        "| Rank | Candidate | OK | Fail | Fallback | Imprecise | Maps | Regions | Typed | Merges |",
        "| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |",
    ]
    for item in summary["ranking"]:
        metrics = item["metrics"]
        lines.append(
            "| {rank} | `{candidate}` | {ok_count} | {failure_count} | {fallback_total} | "
            "{imprecise_region_count} | {memory_map_count} | {region_count} | "
            "{typed_region_count} | "
            "{merge_count} |".format(
                rank=item["rank"],
                candidate=item["candidate"],
                ok_count=item["ok_count"],
                failure_count=item["failure_count"],
                fallback_total=metrics["fallback_total"],
                imprecise_region_count=metrics["imprecise_region_count"],
                memory_map_count=metrics["memory_map_count"],
                region_count=metrics["region_count"],
                typed_region_count=metrics["typed_region_count"],
                merge_count=metrics["merge_count"],
            )
        )

    external_ranking = summary.get("external_ranking") or []
    if external_ranking:
        lines.extend(
            [
                "",
                "## External Memory Partitioner Metrics",
                "",
                (
                    "SVF rows are sidecar MemorySSA metrics. They are not included "
                    "in the main SMACK `$M.*` ranking until an adapter emits sound "
                    "SMACK memory maps."
                ),
                "",
                f"Ranking rule: {summary['external_ranking_rule']}.",
                "",
                (
                    "| Rank | Candidate | OK | Fail | Regions | Avg Size | Max Size | "
                    "Load MU | Store CHI | Phi |"
                ),
                "| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |",
            ]
        )
        for item in external_ranking:
            metrics = item["metrics"]
            lines.append(
                "| {rank} | `{candidate}` | {ok_count} | {failure_count} | "
                "{memory_region_count} | {average_region_size:.3g} | "
                "{max_region_size} | {load_mu_node_count} | "
                "{store_chi_node_count} | {mssa_phi_count} |".format(
                    rank=item["rank"],
                    candidate=item["candidate"],
                    ok_count=item["ok_count"],
                    failure_count=item["failure_count"],
                    memory_region_count=metrics["memory_region_count"],
                    average_region_size=metrics["average_region_size"],
                    max_region_size=metrics["max_region_size"],
                    load_mu_node_count=metrics["load_mu_node_count"],
                    store_chi_node_count=metrics["store_chi_node_count"],
                    mssa_phi_count=metrics["mssa_phi_count"],
                )
            )

    external_candidates = summary.get("external_candidates") or []
    if external_candidates:
        lines.extend(
            [
                "",
                "## External Candidate Probes",
                "",
                "| Candidate | Status | Tool | Reason |",
                "| --- | --- | --- | --- |",
            ]
        )
        for item in external_candidates:
            tool = item.get("tool") or ""
            lines.append(
                "| `{candidate}` | {status} | `{tool}` | {reason} |".format(
                    candidate=item["candidate"],
                    status=item["status"],
                    tool=tool,
                    reason=item["reason"],
                )
            )

    lines.extend(["", "## Failed Runs", ""])
    failed = [record for record in summary["records"] if record["status"] != "ok"]
    if failed:
        for record in failed:
            lines.extend(
                [
                    f"- `{record['candidate']}` on `{record['fixture']}` failed "
                    f"with exit code {record['returncode']}.",
                    "",
                    "```text",
                    str(record.get("error", "")),
                    "```",
                    "",
                ]
            )
    else:
        lines.append("No candidate runs failed.")

    external_failed = [
        record for record in summary.get("external_records", []) if record["status"] != "ok"
    ]
    if external_failed:
        lines.extend(["", "## Failed External Runs", ""])
        for record in external_failed:
            lines.extend(
                [
                    f"- `{record['candidate']}` on `{record['fixture']}` failed "
                    f"with exit code {record['returncode']}.",
                    "",
                    "```text",
                    str(record.get("error", "")),
                    "```",
                    "",
                ]
            )

    path.write_text("\n".join(lines) + "\n")


def run_comparison(
    *,
    repo_root: Path,
    out_dir: Path,
    llvm2bpl: Path,
    clang: Path,
    llvm_link: Path,
    fixtures: list[Fixture],
    candidates: list[Candidate],
    external_probes: list[ExternalProbe],
    svf_extapi: Path | None,
    svf_refined_wpa: Path | None,
    svf_refined_extapi: Path | None,
    svf_refined_mem_par: str,
    svf_native_wpa: Path | None,
    svf_native_extapi: Path | None,
    svf_native_mem_par: str,
    timeout: int,
) -> dict[str, Any]:
    out_dir.mkdir(parents=True, exist_ok=True)
    needs_runtime = any(
        fixture.kind == "source" or (fixture.kind == "bitcode" and fixture.link_runtime)
        for fixture in fixtures
    )
    runtime_bc = (
        _compile_runtime(repo_root=repo_root, out_dir=out_dir, clang=clang, timeout=timeout)
        if needs_runtime
        else None
    )
    records: list[dict[str, Any]] = []
    external_records: list[dict[str, Any]] = []
    raw_candidates = [
        candidate
        for candidate in candidates
        if not (
            svf_refined_wpa is not None
            and _requires_generated_svf_refined_oracle(candidate)
        )
    ]
    for fixture in fixtures:
        linked_bc = _prepare_fixture_bitcode(
            fixture=fixture,
            repo_root=repo_root,
            out_dir=out_dir,
            clang=clang,
            llvm_link=llvm_link,
            runtime_bc=runtime_bc,
            timeout=timeout,
        )
        for candidate in raw_candidates:
            records.append(
                _run_candidate(
                    llvm2bpl=llvm2bpl,
                    linked_bc=linked_bc,
                    fixture=fixture,
                    candidate=candidate,
                    repo_root=repo_root,
                    out_dir=out_dir,
                    timeout=timeout,
                )
            )
        if svf_refined_wpa is not None:
            extapi = infer_svf_extapi_path(svf_refined_wpa, svf_refined_extapi or svf_extapi)
            if extapi is None:
                records.append(
                    {
                        "fixture": fixture.label,
                        "candidate": _svf_refined_label(svf_refined_mem_par),
                        "kind": "integrated-svf-refined",
                        "stage": "setup",
                        "flags": [],
                        "command": [],
                        "returncode": 0,
                        "wall_ms": 0.0,
                        "status": "failed",
                        "error": "SVF extapi.bc not found; pass --svf-refined-extapi",
                    }
                )
            else:
                records.append(
                    _run_svf_refined_candidate(
                        llvm2bpl=llvm2bpl,
                        linked_bc=linked_bc,
                        fixture=fixture,
                        svf_wpa=svf_refined_wpa,
                        svf_extapi=extapi,
                        mem_par=svf_refined_mem_par,
                        repo_root=repo_root,
                        out_dir=out_dir,
                        timeout=timeout,
                    )
                )
        if svf_native_wpa is not None:
            extapi = infer_svf_extapi_path(svf_native_wpa, svf_native_extapi or svf_extapi)
            records.append(
                _run_svf_native_candidate(
                    llvm2bpl=llvm2bpl,
                    linked_bc=linked_bc,
                    fixture=fixture,
                    svf_extapi=extapi,
                    mem_par=svf_native_mem_par,
                    repo_root=repo_root,
                    out_dir=out_dir,
                    timeout=timeout,
                )
            )
        external_records.extend(
            _run_external_partition_candidates(
                linked_bc=linked_bc,
                fixture=fixture,
                external_probes=external_probes,
                repo_root=repo_root,
                svf_extapi=svf_extapi,
                timeout=timeout,
            )
        )
    if not any(record["status"] == "ok" for record in records):
        raise CompareError("all memory partitioning candidate runs failed")
    return build_summary(
        repo_root=repo_root,
        llvm2bpl=llvm2bpl,
        clang=clang,
        llvm_link=llvm_link,
        fixtures=fixtures,
        candidates=[
            *raw_candidates,
            *(
                [
                    Candidate(
                        label=_svf_refined_label(svf_refined_mem_par),
                        flags=(
                            "-sea-dsa=bu",
                            "-smack-memory-partitioner=svf-refined",
                            "-smack-memory-partition-oracle=<generated>",
                        ),
                    )
                ]
                if svf_refined_wpa is not None
                else []
            ),
            *(
                [
                    Candidate(
                        label=_svf_native_label(svf_native_mem_par),
                        flags=(
                            "-smack-memory-partitioner=svf-native",
                            f"-smack-svf-mem-par={svf_native_mem_par}",
                        ),
                    )
                ]
                if svf_native_wpa is not None
                else []
            ),
        ],
        records=records,
        external_probes=external_probes,
        external_records=external_records,
    )


def make_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=_repo_root())
    parser.add_argument("--out-dir", type=Path, default=Path("build/memory-partition-compare"))
    parser.add_argument("--llvm2bpl")
    parser.add_argument("--clang")
    parser.add_argument("--llvm-link")
    parser.add_argument("--timeout", type=int, default=120)
    parser.add_argument(
        "--no-link-runtime",
        action="store_true",
        help="do not link SMACK runtime bitcode into --bc-fixture inputs",
    )
    parser.add_argument(
        "--candidate",
        action="append",
        default=[],
        metavar="NAME=FLAGS",
        help="candidate llvm2bpl flags; may be repeated",
    )
    parser.add_argument(
        "--fixture",
        action="append",
        default=[],
        metavar="NAME=PATH[:ENTRY]",
        help="C fixture to compile and compare; may be repeated",
    )
    parser.add_argument(
        "--bc-fixture",
        action="append",
        default=[],
        metavar="NAME=PATH[:ENTRY]",
        help="LLVM bitcode fixture to compare; may be repeated",
    )
    parser.add_argument(
        "--external-candidate",
        action="append",
        default=[],
        metavar="NAME=TOOL[,TOOL]",
        help=(
            "external analyzer probe; SVF WPA emits sidecar MemorySSA metrics, "
            "other analyzers are reported as skipped until adapters exist; may be repeated"
        ),
    )
    parser.add_argument(
        "--probe-external-candidates",
        action="store_true",
        help="probe common external analyzers such as SVF, cclyzer++, PhASAR, and Phoenix",
    )
    parser.add_argument(
        "--svf-extapi",
        type=Path,
        help="path to SVF extapi.bc for SVF MemorySSA sidecar comparisons",
    )
    parser.add_argument(
        "--svf-refined-wpa",
        type=Path,
        help="SVF wpa executable for integrated svf-refined SMACK map comparison",
    )
    parser.add_argument(
        "--svf-refined-extapi",
        type=Path,
        help="path to SVF extapi.bc for integrated svf-refined SMACK map comparison",
    )
    parser.add_argument(
        "--svf-refined-mem-par",
        choices=SVF_MEM_PAR_MODES,
        default="intra-disjoint",
        help="SVF MemorySSA partition mode for integrated svf-refined candidate",
    )
    parser.add_argument(
        "--svf-native-wpa",
        type=Path,
        help="SVF wpa executable for integrated svf-native SMACK map comparison",
    )
    parser.add_argument(
        "--svf-native-extapi",
        type=Path,
        help="path to SVF extapi.bc for integrated svf-native SMACK map comparison",
    )
    parser.add_argument(
        "--svf-native-mem-par",
        choices=SVF_MEM_PAR_MODES,
        default="intra-disjoint",
        help="SVF MemorySSA partition mode for integrated svf-native candidate",
    )
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = make_arg_parser()
    args = parser.parse_args(argv)

    repo_root = args.repo_root.resolve()
    out_dir = args.out_dir
    if not out_dir.is_absolute():
        out_dir = repo_root / out_dir

    try:
        llvm2bpl = resolve_tool(args.llvm2bpl, "llvm2bpl", repo_root=repo_root)
        clang = resolve_tool(args.clang, "clang", repo_root=repo_root)
        llvm_link = resolve_tool(args.llvm_link, "llvm-link", repo_root=repo_root)
        svf_refined_wpa = None
        if args.svf_refined_wpa is not None:
            svf_refined_wpa = resolve_external_probe_tool(
                ExternalProbe("svf-refined", (str(args.svf_refined_wpa),)),
                repo_root=repo_root,
            )
            if svf_refined_wpa is None:
                raise CompareError(f"SVF wpa not found: {args.svf_refined_wpa}")
        svf_native_wpa = None
        if args.svf_native_wpa is not None:
            svf_native_wpa = resolve_external_probe_tool(
                ExternalProbe("svf-native", (str(args.svf_native_wpa),)),
                repo_root=repo_root,
            )
            if svf_native_wpa is None:
                raise CompareError(f"SVF wpa not found: {args.svf_native_wpa}")
        svf_refined_extapi = (
            resolve_repo_path(args.svf_refined_extapi, repo_root=repo_root)
            if args.svf_refined_extapi
            else None
        )
        svf_native_extapi = (
            resolve_repo_path(args.svf_native_extapi, repo_root=repo_root)
            if args.svf_native_extapi
            else None
        )
        candidates = [parse_candidate(spec) for spec in (args.candidate or DEFAULT_CANDIDATES)]
        fixture_specs = args.fixture or []
        bc_fixture_specs = args.bc_fixture or []
        if not fixture_specs and not bc_fixture_specs:
            fixture_specs = list(DEFAULT_FIXTURES)
        fixtures = [parse_fixture(spec) for spec in fixture_specs]
        fixtures.extend(
            parse_bc_fixture(spec, link_runtime=not args.no_link_runtime)
            for spec in bc_fixture_specs
        )
        external_specs = list(args.external_candidate or [])
        if args.probe_external_candidates:
            external_specs.extend(DEFAULT_EXTERNAL_PROBES)
        external_probes = [parse_external_probe(spec) for spec in external_specs]
        summary = run_comparison(
            repo_root=repo_root,
            out_dir=out_dir,
            llvm2bpl=llvm2bpl,
            clang=clang,
            llvm_link=llvm_link,
            fixtures=fixtures,
            candidates=candidates,
            external_probes=external_probes,
            svf_extapi=args.svf_extapi,
            svf_refined_wpa=svf_refined_wpa,
            svf_refined_extapi=svf_refined_extapi,
            svf_refined_mem_par=args.svf_refined_mem_par,
            svf_native_wpa=svf_native_wpa,
            svf_native_extapi=svf_native_extapi,
            svf_native_mem_par=args.svf_native_mem_par,
            timeout=args.timeout,
        )
    except CompareError as exc:
        parser.error(str(exc))

    json_path = out_dir / "partition-comparison.json"
    md_path = out_dir / "partition-comparison.md"
    json_path.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    write_markdown(summary, md_path)
    print(f"wrote {json_path}")
    print(f"wrote {md_path}")
    best = summary["ranking"][0]
    print(f"best candidate: {best['candidate']} (rank {best['rank']})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Compare indirect-call devirtualization precision across analyzers.

The built-in candidates run SMACK/llvm2bpl with different analysis flags and
read the canonical ``-smack-devirt-report`` JSON. External candidates run SVF or
PhASAR as hard comparison dependencies and normalize their call-target output
against the same SMACK callsite inventory.
"""

from __future__ import annotations

import argparse
import json
import re
import shlex
import shutil
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any

SCHEMA_VERSION = 2
SUPPORTED_REPORT_SCHEMAS = {1, 2}

DEFAULT_CANDIDATES = (
    "smack-default=-smack-memory-partitioner=sea-dsa",
    "sea-dsa-ci=-sea-dsa=ci -smack-memory-partitioner=sea-dsa",
    "sea-dsa-bu=-sea-dsa=bu -smack-memory-partitioner=sea-dsa",
    "sea-dsa-butd-cs=-sea-dsa=butd-cs -smack-memory-partitioner=sea-dsa",
    "sea-dsa-cs=-sea-dsa=cs -smack-memory-partitioner=sea-dsa",
    "sea-dsa-flat=-sea-dsa=flat -smack-memory-partitioner=sea-dsa",
    (
        "teadsa-butd-cs-type-aware=-sea-dsa=butd-cs -sea-dsa-type-aware "
        "-smack-memory-partitioner=sea-dsa"
    ),
)

DEFAULT_FIXTURES = (
    "func_ptr=test/c/data/func_ptr.c:main",
    "struct_alias=test/c/data/struct_alias.c:main",
)

DEFAULT_EXTERNAL_CANDIDATES = (
    "svf-local-ander=svf-devirt-oracle,svf-local-devirt",
    "phasar-vta=phasar-cli,phasar-llvm,phasar",
)

SVF_ANALYSIS_FLAGS = {
    "ander": ("-ander",),
    "sander": ("-sander",),
    "sfrander": ("-sfrander",),
    "steens": ("-steens",),
    "type": ("-type",),
    "fspta": ("-fspta",),
    "vfspta": ("-vfspta",),
}

SVF_LABEL_OPTION_FLAGS = {
    "model-arrays": "-model-arrays",
    "model-consts": "-model-consts",
    "pre-field": "-pre-field-sensitive",
    "vt-in-ir": "-vt-in-ir",
}

BEARSSL_DRIVER_TARGET_ORACLE = {
    ("bearssl_devirt_hash_entry", 69): (
        "br_md5sha1_init",
        "br_sha1_init",
        "br_sha256_init",
        "br_sha512_init",
    ),
    ("bearssl_devirt_hash_entry", 70): (
        "br_md5sha1_update",
        "br_sha1_update",
        "br_sha224_update",
        "br_sha384_update",
    ),
    ("bearssl_devirt_hash_entry", 71): (
        "br_md5sha1_out",
        "br_sha1_out",
        "br_sha256_out",
        "br_sha512_out",
    ),
    ("bearssl_devirt_hash_entry", 72): (
        "br_md5sha1_state",
        "br_sha1_state",
        "br_sha224_state",
        "br_sha384_state",
    ),
    ("bearssl_devirt_block_entry", 87): (
        "br_aes_big_cbcenc_init",
        "br_aes_ct64_cbcenc_init",
        "br_aes_ct_cbcenc_init",
        "br_aes_small_cbcenc_init",
    ),
    ("bearssl_devirt_block_entry", 88): (
        "br_aes_big_cbcenc_run",
        "br_aes_ct64_cbcenc_run",
        "br_aes_ct_cbcenc_run",
        "br_aes_small_cbcenc_run",
    ),
    ("bearssl_devirt_block_entry", 89): (
        "br_aes_big_ctr_init",
        "br_aes_ct64_ctr_init",
        "br_aes_ct_ctr_init",
        "br_aes_small_ctr_init",
    ),
    ("bearssl_devirt_block_entry", 90): (
        "br_aes_big_ctr_run",
        "br_aes_ct64_ctr_run",
        "br_aes_ct_ctr_run",
        "br_aes_small_ctr_run",
    ),
}


@dataclass(frozen=True)
class Candidate:
    label: str
    flags: tuple[str, ...]


@dataclass(frozen=True)
class ExternalCandidate:
    label: str
    tools: tuple[str, ...]


@dataclass(frozen=True)
class Fixture:
    label: str
    source: Path
    entry_point: str = "main"
    kind: str = "source"
    link_runtime: bool = True


@dataclass(frozen=True)
class ExternalObservation:
    targets: tuple[str, ...]
    callsite_id: str | None = None
    function: str | None = None
    file: str | None = None
    line: int | None = None
    column: int | None = None
    instruction: str | None = None


@dataclass(frozen=True)
class ExternalInput:
    candidate: str
    fixture: str
    path: Path


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


def load_analyzer_manifest(path: Path, *, repo_root: Path) -> dict[str, Any]:
    manifest_path = resolve_repo_path(path, repo_root=repo_root)
    try:
        manifest = json.loads(manifest_path.read_text())
    except FileNotFoundError as exc:
        raise CompareError(f"analyzer manifest not found: {manifest_path}") from exc
    except json.JSONDecodeError as exc:
        raise CompareError(f"malformed analyzer manifest: {manifest_path}") from exc

    if not isinstance(manifest, dict):
        raise CompareError(f"analyzer manifest must be a JSON object: {manifest_path}")
    analyzers = manifest.get("analyzers", {})
    if not isinstance(analyzers, dict):
        raise CompareError(f"analyzer manifest has invalid analyzers object: {manifest_path}")

    manifest = dict(manifest)
    manifest["manifest_path"] = str(manifest_path)
    return manifest


def _candidate_analyzer_key(label: str) -> str:
    lowered = label.lower()
    if lowered.startswith("svf"):
        return "svf"
    if lowered.startswith("phasar"):
        return "phasar"
    return lowered.split("-", 1)[0]


def svf_flags_for_candidate(label: str) -> tuple[str, ...]:
    lowered = label.lower()
    if lowered == "svf":
        analysis = "ander"
    elif lowered.startswith("svf-local-"):
        analysis = lowered.removeprefix("svf-local-").split("-", 1)[0]
    elif lowered.startswith("svf-"):
        analysis = lowered.removeprefix("svf-").split("-", 1)[0]
    else:
        analysis = "ander"

    flags = list(SVF_ANALYSIS_FLAGS.get(analysis, SVF_ANALYSIS_FLAGS["ander"]))
    for marker, flag in SVF_LABEL_OPTION_FLAGS.items():
        if marker in lowered and flag not in flags:
            flags.append(flag)
    return tuple(flags)


def is_svf_local_candidate(label: str) -> bool:
    return label.lower().startswith("svf-local")


def _manifest_paths(value: Any, *, repo_root: Path, manifest: dict[str, Any]) -> list[Path]:
    paths: list[Path] = []
    manifest_base = Path(str(manifest.get("manifest_path", repo_root))).parent
    if isinstance(value, str) and value:
        path = Path(value)
        if path.is_absolute():
            paths.append(path)
        else:
            paths.extend([manifest_base / path, repo_root / path])
    elif isinstance(value, list):
        for item in value:
            paths.extend(_manifest_paths(item, repo_root=repo_root, manifest=manifest))
    elif isinstance(value, dict):
        for item in value.values():
            paths.extend(_manifest_paths(item, repo_root=repo_root, manifest=manifest))
    return paths


def _manifest_tool_candidates(
    candidate: ExternalCandidate,
    *,
    repo_root: Path,
    manifest: dict[str, Any] | None,
) -> list[Path]:
    if not manifest:
        return []

    analyzers = manifest.get("analyzers", {})
    if not isinstance(analyzers, dict):
        return []

    analyzer = analyzers.get(_candidate_analyzer_key(candidate.label), {})
    if not isinstance(analyzer, dict):
        return []

    tools = analyzer.get("tools", {})
    if not isinstance(tools, dict):
        return []

    paths: list[Path] = []
    wanted = set(candidate.tools)
    for name in candidate.tools:
        paths.extend(_manifest_paths(tools.get(name), repo_root=repo_root, manifest=manifest))
    for name, value in tools.items():
        if name not in wanted:
            paths.extend(_manifest_paths(value, repo_root=repo_root, manifest=manifest))
    return paths


def _manifest_llvm_tool(
    candidate: ExternalCandidate,
    tool_name: str,
    *,
    repo_root: Path,
    manifest: dict[str, Any] | None,
) -> Path | None:
    if not manifest:
        return None
    analyzers = manifest.get("analyzers", {})
    if not isinstance(analyzers, dict):
        return None
    analyzer = analyzers.get(_candidate_analyzer_key(candidate.label), {})
    if not isinstance(analyzer, dict):
        return None
    llvm_tools = analyzer.get("llvm_tools", {})
    if not isinstance(llvm_tools, dict):
        return None
    for path in _manifest_paths(llvm_tools.get(tool_name), repo_root=repo_root, manifest=manifest):
        if path.exists():
            return path.resolve()
    return None


def _manifest_analyzer(
    candidate: ExternalCandidate,
    *,
    manifest: dict[str, Any] | None,
) -> dict[str, Any]:
    if not manifest:
        return {}
    analyzers = manifest.get("analyzers", {})
    if not isinstance(analyzers, dict):
        return {}
    analyzer = analyzers.get(_candidate_analyzer_key(candidate.label), {})
    return analyzer if isinstance(analyzer, dict) else {}


def _manifest_svf_extapi(
    candidate: ExternalCandidate,
    *,
    repo_root: Path,
    manifest: dict[str, Any] | None,
) -> Path | None:
    analyzer = _manifest_analyzer(candidate, manifest=manifest)
    install_dir = analyzer.get("install_dir")
    if isinstance(install_dir, str):
        path = Path(install_dir) / "lib" / "extapi.bc"
        if path.exists():
            return path.resolve()
    tools = analyzer.get("tools", {})
    if isinstance(tools, dict):
        for value in tools.values():
            if isinstance(value, str):
                path = Path(value).resolve().parent.parent / "lib" / "extapi.bc"
                if path.exists():
                    return path.resolve()
    for path in _manifest_paths("lib/extapi.bc", repo_root=repo_root, manifest=manifest or {}):
        if path.exists():
            return path.resolve()
    return None


def resolve_external_tool(
    candidate: ExternalCandidate,
    *,
    repo_root: Path,
    manifest: dict[str, Any] | None = None,
) -> Path:
    manifest_candidates = _manifest_tool_candidates(candidate, repo_root=repo_root, manifest=manifest)
    for tool in [*manifest_candidates, *(Path(name) for name in candidate.tools)]:
        tool_text = str(tool)
        if tool_text.startswith("json:"):
            path = Path(tool_text.removeprefix("json:"))
            if not path.is_absolute():
                path = repo_root / path
            if path.exists():
                return path.resolve()
            raise CompareError(f"external JSON report not found for {candidate.label}: {path}")

        path = Path(tool_text)
        if not path.is_absolute():
            repo_path = repo_root / path
            if repo_path.exists():
                return repo_path.resolve()
        elif path.exists():
            return path.resolve()

        found = shutil.which(tool_text)
        if found:
            return Path(found).resolve()

    raise CompareError(
        f"external analyzer '{candidate.label}' requires one of: "
        f"{', '.join(candidate.tools)}"
    )


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


def parse_external_candidate(spec: str) -> ExternalCandidate:
    if "=" not in spec:
        raise CompareError(f"external candidate must use NAME=TOOL[,TOOL] syntax: {spec}")
    label, tools_text = spec.split("=", 1)
    label = label.strip()
    tools = tuple(tool.strip() for tool in tools_text.split(",") if tool.strip())
    if not label:
        raise CompareError(f"external candidate label is empty: {spec}")
    if not tools:
        raise CompareError(f"external candidate tools are empty: {spec}")
    return ExternalCandidate(label=label, tools=tools)


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


def parse_bc_fixture(spec: str, *, link_runtime: bool = True) -> Fixture:
    fixture = parse_fixture(spec)
    return Fixture(
        label=fixture.label,
        source=fixture.source,
        entry_point=fixture.entry_point,
        kind="bitcode",
        link_runtime=link_runtime,
    )


def parse_external_input(spec: str) -> ExternalInput:
    if "=" not in spec:
        raise CompareError(
            f"external input must use CANDIDATE:FIXTURE=PATH syntax: {spec}"
        )
    key, path_text = spec.split("=", 1)
    candidate, separator, fixture = key.partition(":")
    if not separator or not candidate or not fixture:
        raise CompareError(
            f"external input must use CANDIDATE:FIXTURE=PATH syntax: {spec}"
        )
    return ExternalInput(candidate=candidate, fixture=fixture, path=Path(path_text))


def resolve_repo_path(path: Path, *, repo_root: Path) -> Path:
    return path if path.is_absolute() else repo_root / path


def _require_nonnegative_int(value: Any, field: str) -> int:
    if not isinstance(value, int) or value < 0:
        raise CompareError(f"expected nonnegative integer {field}, got {value!r}")
    return value


def _normalize_callsite(callsite: dict[str, Any], *, index: int) -> dict[str, Any]:
    normalized = dict(callsite)
    function = normalized.get("function")
    if not isinstance(function, str) or not function:
        raise CompareError(f"devirt report callsite {index} missing function")

    callsite_id = normalized.get("callsite_id")
    if not isinstance(callsite_id, str) or not callsite_id:
        callsite_id = f"{function}:indirect:{index}"
        normalized["callsite_id"] = callsite_id
    normalized.setdefault("callsite_index", index)
    normalized.setdefault("file", None)
    normalized.setdefault("line", 0)
    normalized.setdefault("column", 0)
    normalized.setdefault("instruction", "")
    normalized.setdefault("complete", False)
    normalized.setdefault("sea_dsa_complete", False)
    normalized.setdefault("sea_dsa_target_count", 0)
    normalized.setdefault("fallback_target_count", 0)
    normalized.setdefault("source", "unknown")
    normalized.setdefault("reason", "")

    targets = normalized.get("targets", [])
    if not isinstance(targets, list) or not all(isinstance(target, str) for target in targets):
        raise CompareError(f"devirt report callsite {index} has invalid targets")
    normalized["targets"] = sorted(set(targets))
    normalized["target_count"] = len(normalized["targets"])

    for field in (
        "callsite_index",
        "line",
        "column",
        "sea_dsa_target_count",
        "fallback_target_count",
        "target_count",
    ):
        _require_nonnegative_int(normalized.get(field), field)
    if not isinstance(normalized.get("complete"), bool):
        raise CompareError(f"devirt report callsite {index} has non-bool complete")
    return normalized


def load_devirt_report(path: Path) -> dict[str, Any]:
    try:
        data = json.loads(path.read_text())
    except json.JSONDecodeError as exc:
        raise CompareError(f"malformed JSON report: {path}") from exc

    if data.get("schema_version") not in SUPPORTED_REPORT_SCHEMAS:
        raise CompareError(f"unsupported devirt report schema in {path}")
    callsites = data.get("callsites")
    if not isinstance(callsites, list):
        raise CompareError(f"devirt report missing callsites list: {path}")

    normalized = dict(data)
    normalized["schema_version"] = SCHEMA_VERSION
    normalized["callsites"] = [
        _normalize_callsite(callsite, index=index)
        for index, callsite in enumerate(callsites)
        if isinstance(callsite, dict)
    ]
    if len(normalized["callsites"]) != len(callsites):
        raise CompareError(f"devirt report contains non-object callsite: {path}")
    return normalized


def expected_targets_for_callsite(fixture: str, callsite: dict[str, Any]) -> tuple[str, ...] | None:
    if fixture != "bearssl":
        return None
    try:
        line = int(callsite.get("line") or 0)
    except (TypeError, ValueError):
        line = 0
    key = (str(callsite.get("function", "")), line)
    return BEARSSL_DRIVER_TARGET_ORACLE.get(key)


def annotate_report_with_oracle(report: dict[str, Any], *, fixture: str) -> dict[str, Any]:
    annotated = dict(report)
    annotated_callsites: list[dict[str, Any]] = []
    for callsite in report.get("callsites", []):
        call = dict(callsite)
        expected = expected_targets_for_callsite(fixture, call)
        if expected is not None:
            targets = set(str(target) for target in call.get("targets", []))
            expected_set = set(expected)
            missing = sorted(expected_set - targets)
            spurious = sorted(targets - expected_set)
            call.update(
                {
                    "expected_targets": sorted(expected_set),
                    "expected_target_count": len(expected_set),
                    "oracle_sound": not missing,
                    "oracle_exact": not missing and not spurious,
                    "missing_targets": missing,
                    "spurious_targets": spurious,
                }
            )
        annotated_callsites.append(call)
    annotated["callsites"] = annotated_callsites
    return annotated


def devirt_metrics(report: dict[str, Any]) -> dict[str, Any]:
    callsites = report.get("callsites", [])
    complete = [call for call in callsites if call.get("complete") is True]
    fallback = [
        call
        for call in callsites
        if call.get("source") == "fallback" or call.get("complete") is not True
    ]
    target_counts = [int(call.get("target_count", 0)) for call in callsites]
    complete_target_counts = [int(call.get("target_count", 0)) for call in complete]
    oracle_callsites = [call for call in callsites if "expected_targets" in call]
    return {
        "total_callsites": len(callsites),
        "complete_callsites": len(complete),
        "incomplete_callsites": len(callsites) - len(complete),
        "fallback_callsites": len(fallback),
        "singleton_callsites": sum(1 for call in complete if int(call["target_count"]) == 1),
        "empty_target_callsites": sum(1 for count in target_counts if count == 0),
        "target_total": sum(target_counts),
        "complete_target_total": sum(complete_target_counts),
        "fallback_target_total": sum(
            int(call.get("fallback_target_count", 0)) for call in callsites
        ),
        "max_target_count": max(target_counts, default=0),
        "max_complete_target_count": max(complete_target_counts, default=0),
        "average_target_count": (
            float(sum(target_counts)) / float(len(target_counts)) if target_counts else 0.0
        ),
        "oracle_callsites": len(oracle_callsites),
        "oracle_sound_callsites": sum(
            1 for call in oracle_callsites if call.get("oracle_sound") is True
        ),
        "oracle_exact_callsites": sum(
            1 for call in oracle_callsites if call.get("oracle_exact") is True
        ),
        "oracle_unsound_callsites": sum(
            1 for call in oracle_callsites if call.get("oracle_sound") is not True
        ),
        "oracle_missing_target_total": sum(
            len(call.get("missing_targets", [])) for call in oracle_callsites
        ),
        "oracle_spurious_target_total": sum(
            len(call.get("spurious_targets", [])) for call in oracle_callsites
        ),
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
    run_command([str(llvm_link), str(bc), str(runtime_bc), "-o", str(linked)], cwd=repo_root, timeout=timeout)
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
    run_command([str(llvm_link), str(source), str(runtime_bc), "-o", str(linked)], cwd=repo_root, timeout=timeout)
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


def _error_tail(output: str, *, limit: int = 30) -> str:
    return "\n".join(output.splitlines()[-limit:])


def _run_smack_candidate(
    *,
    llvm2bpl: Path,
    linked_bc: Path,
    fixture: Fixture,
    candidate: Candidate,
    repo_root: Path,
    out_dir: Path,
    timeout: int,
) -> dict[str, Any]:
    report_path = out_dir / f"{fixture.label}.{candidate.label}.devirt.json"
    bpl_path = out_dir / f"{fixture.label}.{candidate.label}.bpl"
    command = [
        str(llvm2bpl),
        *candidate.flags,
        f"--entry-points={fixture.entry_point}",
        f"--bpl={bpl_path}",
        f"-smack-devirt-report={report_path}",
        str(linked_bc),
    ]

    start = time.monotonic()
    completed = run_command(command, cwd=repo_root, timeout=timeout, check=False)
    wall_ms = (time.monotonic() - start) * 1000.0
    base: dict[str, Any] = {
        "fixture": fixture.label,
        "candidate": candidate.label,
        "kind": "smack",
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
        report = load_devirt_report(report_path)
    except CompareError as exc:
        base.update({"status": "failed", "error": str(exc)})
        return base

    report = annotate_report_with_oracle(report, fixture=fixture.label)
    report_path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    base.update({"status": "ok", "report": report, "metrics": devirt_metrics(report)})
    return base


def _target_names(text: str) -> tuple[str, ...]:
    names = set()
    for raw in re.findall(r"@?([A-Za-z_.$][A-Za-z0-9_.$]*)", text):
        if raw.lower() in {
            "callsite",
            "location",
            "targets",
            "target",
            "nodeid",
            "with",
            "null",
        }:
            continue
        names.add(raw)
    return tuple(sorted(names))


def parse_svf_output(output: str) -> list[ExternalObservation]:
    observations: list[ExternalObservation] = []
    current: dict[str, Any] | None = None
    collecting_targets = False

    def flush_current() -> None:
        nonlocal current, collecting_targets
        if current and current["targets"]:
            observations.append(
                ExternalObservation(
                    function=current.get("function"),
                    file=current.get("file"),
                    line=current.get("line"),
                    column=current.get("column"),
                    instruction=current.get("instruction"),
                    targets=tuple(sorted(current["targets"])),
                )
            )
        current = None
        collecting_targets = False

    for line in output.splitlines():
        lowered = line.lower()
        if line.startswith("NodeID:") or line.startswith("****"):
            flush_current()
            continue
        if "callsite:" not in lowered:
            if current is not None:
                if "with Targets:" in line or "Targets:" in line:
                    targets_text = line.split("with Targets:", 1)[-1].split("Targets:", 1)[-1]
                    current["targets"].update(_target_names(targets_text))
                    collecting_targets = True
                elif "!!!has no targets" in line:
                    collecting_targets = False
                elif collecting_targets:
                    stripped = line.strip()
                    if not stripped:
                        flush_current()
                    else:
                        current["targets"].update(_target_names(stripped))
            continue

        flush_current()
        callsite_text = line.split("CallSite:", 1)[1]
        instruction = callsite_text
        location_text = ""
        if "Location:" in callsite_text:
            instruction, location_text = callsite_text.split("Location:", 1)
        targets_text = ""
        if "with Targets:" in line:
            targets_text = line.split("with Targets:", 1)[1]
        elif "Targets:" in line:
            targets_text = line.split("Targets:", 1)[1]

        file_name: str | None = None
        line_no: int | None = None
        column_no: int | None = None
        match = re.search(r"([^\s:]+):(\d+):?(\d+)?", location_text)
        if match:
            file_name = match.group(1)
            line_no = int(match.group(2))
            if match.group(3):
                column_no = int(match.group(3))
        jsonish_match = re.search(
            r'"ln":\s*(\d+),\s*"cl":\s*(\d+),\s*"fl":\s*"([^"]+)"',
            line,
        )
        if jsonish_match:
            line_no = int(jsonish_match.group(1))
            column_no = int(jsonish_match.group(2))
            file_name = jsonish_match.group(3)
        fun_match = re.search(r"\{fun:\s*([A-Za-z_.$][A-Za-z0-9_.$]*)", line)
        function_name = fun_match.group(1) if fun_match else None

        targets = _target_names(targets_text)
        current = {
            "instruction": instruction.strip(),
            "function": function_name,
            "file": file_name,
            "line": line_no,
            "column": column_no,
            "targets": set(targets),
        }
        collecting_targets = "with Targets:" in line or "Targets:" in line
    flush_current()
    return observations


def _walk_json(value: Any) -> list[Any]:
    items = [value]
    if isinstance(value, dict):
        for child in value.values():
            items.extend(_walk_json(child))
    elif isinstance(value, list):
        for child in value:
            items.extend(_walk_json(child))
    return items


def parse_phasar_results(value: Any) -> list[ExternalObservation]:
    observations: list[ExternalObservation] = []
    by_callsite: dict[str, set[str]] = {}
    for item in _walk_json(value):
        if not isinstance(item, dict):
            continue
        callsite = item.get("callsite") or item.get("callSite") or item.get("source")
        target = item.get("target") or item.get("callee") or item.get("destination")
        if isinstance(callsite, str) and isinstance(target, str):
            by_callsite.setdefault(callsite, set()).add(target)

    for callsite, targets in by_callsite.items():
        observations.append(
        ExternalObservation(instruction=callsite, targets=tuple(sorted(targets)))
    )
    return observations


def parse_phasar_callgraph_json(value: Any) -> list[ExternalObservation]:
    by_line: dict[int, set[str]] = {}
    if not isinstance(value, dict):
        return []
    for target, callsites in value.items():
        if not isinstance(target, str) or not isinstance(callsites, list):
            continue
        if target.startswith("__psr") or target.startswith("llvm."):
            continue
        for callsite in callsites:
            if isinstance(callsite, int) and callsite > 0:
                by_line.setdefault(callsite, set()).add(target)
    return [
        ExternalObservation(line=line, targets=tuple(sorted(targets)))
        for line, targets in sorted(by_line.items())
    ]


def parse_phasar_output(output: str) -> list[ExternalObservation]:
    observations: list[ExternalObservation] = []
    by_callsite: dict[str, set[str]] = {}
    for line in output.splitlines():
        if "->" not in line:
            continue
        caller, callee = line.split("->", 1)
        callee_names = _target_names(callee)
        if callee_names:
            by_callsite.setdefault(caller.strip(), set()).update(callee_names)
    for callsite, targets in by_callsite.items():
        observations.append(
            ExternalObservation(instruction=callsite, targets=tuple(sorted(targets)))
        )
    return observations


def _callsite_match_key(callsite: dict[str, Any]) -> tuple[Any, ...]:
    return (
        callsite.get("function"),
        callsite.get("file"),
        callsite.get("line"),
        callsite.get("column"),
    )


def canonicalize_external_report(
    *,
    inventory: dict[str, Any],
    observations: list[ExternalObservation],
    candidate: str,
    adapter: str,
) -> dict[str, Any]:
    inventory_callsites = inventory.get("callsites", [])
    by_id = {call["callsite_id"]: call for call in inventory_callsites}
    by_location = {_callsite_match_key(call): call for call in inventory_callsites}
    by_line: dict[int, dict[str, Any] | None] = {}
    for call in inventory_callsites:
        line = call.get("line")
        if isinstance(line, int) and line > 0:
            by_line[line] = call if line not in by_line else None
    matched: dict[str, ExternalObservation] = {}

    for observation in observations:
        call = None
        if observation.callsite_id and observation.callsite_id in by_id:
            call = by_id[observation.callsite_id]
        if call is None and observation.function:
            key = (observation.function, observation.file, observation.line, observation.column)
            call = by_location.get(key)
        if call is None and observation.line:
            call = by_line.get(observation.line)
        if call is None and observation.instruction:
            needle = " ".join(observation.instruction.split())
            for candidate_call in inventory_callsites:
                haystack = " ".join(str(candidate_call.get("instruction", "")).split())
                if needle and (needle in haystack or haystack in needle):
                    call = candidate_call
                    break
        if call is not None:
            matched[str(call["callsite_id"])] = observation

    out_callsites: list[dict[str, Any]] = []
    for call in inventory_callsites:
        observation = matched.get(str(call["callsite_id"]))
        targets = sorted(set(observation.targets)) if observation else []
        out_callsites.append(
            {
                "callsite_id": call["callsite_id"],
                "callsite_index": call.get("callsite_index", 0),
                "function": call["function"],
                "file": call.get("file"),
                "line": call.get("line", 0),
                "column": call.get("column", 0),
                "instruction": call.get("instruction", ""),
                "complete": bool(targets),
                "sea_dsa_complete": False,
                "sea_dsa_target_count": 0,
                "fallback_target_count": 0 if targets else int(call.get("fallback_target_count", 0)),
                "target_count": len(targets),
                "source": adapter,
                "reason": "external-targets" if targets else "external-unmatched-callsite",
                "targets": targets,
            }
        )

    return {
        "schema_version": SCHEMA_VERSION,
        "module": inventory.get("module", ""),
        "candidate": candidate,
        "adapter": adapter,
        "callsites": out_callsites,
    }


def _match_external_callsite(
    *,
    callsite: dict[str, Any],
    inventory_callsites: list[dict[str, Any]],
    by_id: dict[str, dict[str, Any]],
    by_location: dict[tuple[Any, ...], dict[str, Any]],
    by_function_line_column: dict[tuple[Any, ...], dict[str, Any] | None],
    by_line: dict[int, dict[str, Any] | None],
) -> dict[str, Any] | None:
    function = callsite.get("function")
    if isinstance(function, str):
        key = (
            function,
            callsite.get("file"),
            callsite.get("line"),
            callsite.get("column"),
        )
        matched = by_location.get(key)
        if matched is not None:
            return matched
        line = callsite.get("line")
        column = callsite.get("column")
        if isinstance(line, int) and isinstance(column, int):
            matched = by_function_line_column.get((function, line, column))
            if matched is not None:
                return matched
        return None

    callsite_id = callsite.get("callsite_id")
    if isinstance(callsite_id, str) and callsite_id in by_id:
        return by_id[callsite_id]

    line = callsite.get("line")
    if isinstance(line, int) and line > 0:
        matched = by_line.get(line)
        if matched is not None:
            return matched

    instruction = callsite.get("instruction")
    if isinstance(instruction, str):
        needle = " ".join(instruction.split())
        for candidate_call in inventory_callsites:
            haystack = " ".join(str(candidate_call.get("instruction", "")).split())
            if needle and (needle in haystack or haystack in needle):
                return candidate_call
    return None


def canonicalize_external_devirt_report(
    *,
    inventory: dict[str, Any],
    report: dict[str, Any],
    candidate: str,
    adapter: str,
) -> dict[str, Any]:
    inventory_callsites = inventory.get("callsites", [])
    by_id = {call["callsite_id"]: call for call in inventory_callsites}
    by_location = {_callsite_match_key(call): call for call in inventory_callsites}
    by_function_line_column: dict[tuple[Any, ...], dict[str, Any] | None] = {}
    by_line: dict[int, dict[str, Any] | None] = {}
    for call in inventory_callsites:
        line = call.get("line")
        function = call.get("function")
        column = call.get("column")
        if isinstance(function, str) and isinstance(line, int) and isinstance(column, int):
            key = (function, line, column)
            by_function_line_column[key] = (
                call if key not in by_function_line_column else None
            )
        if isinstance(line, int) and line > 0:
            by_line[line] = call if line not in by_line else None

    matched: dict[str, dict[str, Any]] = {}
    for callsite in report.get("callsites", []):
        call = _match_external_callsite(
            callsite=callsite,
            inventory_callsites=inventory_callsites,
            by_id=by_id,
            by_location=by_location,
            by_function_line_column=by_function_line_column,
            by_line=by_line,
        )
        if call is not None:
            matched[str(call["callsite_id"])] = callsite

    out_callsites: list[dict[str, Any]] = []
    for call in inventory_callsites:
        raw = matched.get(str(call["callsite_id"]))
        targets = sorted(set(raw.get("targets", []))) if raw else []
        if not all(isinstance(target, str) for target in targets):
            raise CompareError(f"external report has invalid targets for {candidate}")
        complete = bool(raw.get("complete")) if raw else False
        out_call = {
            "callsite_id": call["callsite_id"],
            "callsite_index": call.get("callsite_index", 0),
            "function": call["function"],
            "file": call.get("file"),
            "line": call.get("line", 0),
            "column": call.get("column", 0),
            "instruction": call.get("instruction", ""),
            "complete": complete,
            "sea_dsa_complete": False,
            "sea_dsa_target_count": 0,
            "fallback_target_count": 0 if targets else int(call.get("fallback_target_count", 0)),
            "target_count": len(targets),
            "source": str(raw.get("source", adapter)) if raw else adapter,
            "reason": (
                str(raw.get("reason", "external-targets"))
                if raw
                else "external-unmatched-callsite"
            ),
            "targets": targets,
        }
        if raw:
            for key, value in raw.items():
                if key.startswith("svf_") or key == "points_to_count":
                    out_call[key] = value
        out_callsites.append(out_call)

    return {
        "schema_version": SCHEMA_VERSION,
        "module": inventory.get("module", ""),
        "candidate": candidate,
        "adapter": adapter,
        "callsites": out_callsites,
    }


def load_external_json_report(path: Path, *, inventory: dict[str, Any], candidate: str) -> dict[str, Any]:
    data = load_devirt_report(path)
    observations = [
        ExternalObservation(
            callsite_id=call.get("callsite_id"),
            function=call.get("function"),
            file=call.get("file"),
            line=call.get("line"),
            column=call.get("column"),
            instruction=call.get("instruction"),
            targets=tuple(call.get("targets", [])),
        )
        for call in data.get("callsites", [])
    ]
    return canonicalize_external_report(
        inventory=inventory,
        observations=observations,
        candidate=candidate,
        adapter="external-json",
    )


def _llvm_disassemble(
    *,
    linked_bc: Path,
    llvm_dis: Path,
    out_dir: Path,
    fixture: Fixture,
    timeout: int,
    repo_root: Path,
) -> Path:
    ll_path = out_dir / f"{fixture.label}.ll"
    run_command(
        [str(llvm_dis), str(linked_bc), "-o", str(ll_path)],
        cwd=repo_root,
        timeout=timeout,
    )
    return ll_path


def _external_input_for(
    *,
    external_inputs: dict[tuple[str, str], Path],
    external: ExternalCandidate,
    fixture: Fixture,
    linked_bc: Path,
    repo_root: Path,
) -> Path:
    analyzer_key = _candidate_analyzer_key(external.label)
    for key in (
        (external.label, fixture.label),
        (analyzer_key, fixture.label),
        ("*", fixture.label),
    ):
        path = external_inputs.get(key)
        if path is not None:
            resolved = resolve_repo_path(path, repo_root=repo_root)
            if not resolved.exists():
                raise CompareError(
                    f"external analyzer input not found for {external.label} "
                    f"on {fixture.label}: {resolved}"
                )
            return resolved
    return linked_bc


def _llvm_ir_for_external(
    *,
    external_input: Path,
    linked_bc: Path,
    llvm_dis: Path | None,
    manifest: dict[str, Any] | None,
    external: ExternalCandidate,
    out_dir: Path,
    fixture: Fixture,
    timeout: int,
    repo_root: Path,
) -> Path:
    if external_input.suffix == ".ll":
        return external_input
    disassembler = _manifest_llvm_tool(
        external,
        "llvm-dis",
        repo_root=repo_root,
        manifest=manifest,
    ) or llvm_dis
    if disassembler is None:
        raise CompareError("PhASAR comparison requires llvm-dis")
    return _llvm_disassemble(
        linked_bc=external_input if external_input != linked_bc else linked_bc,
        llvm_dis=disassembler,
        out_dir=out_dir,
        fixture=fixture,
        timeout=timeout,
        repo_root=repo_root,
    )


def _run_external_candidate(
    *,
    linked_bc: Path,
    fixture: Fixture,
    external: ExternalCandidate,
    inventory: dict[str, Any],
    repo_root: Path,
    out_dir: Path,
    llvm_dis: Path | None,
    analyzer_manifest: dict[str, Any] | None,
    external_inputs: dict[tuple[str, str], Path],
    timeout: int,
) -> dict[str, Any]:
    start = time.monotonic()
    base: dict[str, Any] = {
        "fixture": fixture.label,
        "candidate": external.label,
        "kind": "external",
        "flags": [],
        "returncode": 0,
        "wall_ms": 0.0,
    }

    try:
        tool = resolve_external_tool(external, repo_root=repo_root, manifest=analyzer_manifest)
        external_input = _external_input_for(
            external_inputs=external_inputs,
            external=external,
            fixture=fixture,
            linked_bc=linked_bc,
            repo_root=repo_root,
        )
        if str(tool).endswith(".json") or external.tools[0].startswith("json:"):
            report = load_external_json_report(tool, inventory=inventory, candidate=external.label)
            command = [f"json:{tool}"]
            completed = subprocess.CompletedProcess(command, 0, "")
        elif is_svf_local_candidate(external.label):
            command = [str(tool), *svf_flags_for_candidate(external.label)]
            extapi = _manifest_svf_extapi(
                external,
                repo_root=repo_root,
                manifest=analyzer_manifest,
            )
            if extapi is not None:
                command.append(f"-extapi={extapi}")
            local_report_path = out_dir / f"{fixture.label}.{external.label}.raw.devirt.json"
            command.extend(
                [
                    "--candidate",
                    external.label,
                    "--entry-function",
                    fixture.entry_point,
                    "--out",
                    str(local_report_path),
                    str(external_input),
                ]
            )
            completed = run_command(command, cwd=repo_root, timeout=timeout, check=False)
            if completed.returncode == 0:
                raw_report = load_devirt_report(local_report_path)
                report = canonicalize_external_devirt_report(
                    inventory=inventory,
                    report=raw_report,
                    candidate=external.label,
                    adapter="svf-local-slot",
                )
            else:
                report = canonicalize_external_report(
                    inventory=inventory,
                    observations=[],
                    candidate=external.label,
                    adapter="svf-local-slot",
                )
        elif external.label.startswith("svf"):
            command = [str(tool), *svf_flags_for_candidate(external.label)]
            extapi = _manifest_svf_extapi(
                external,
                repo_root=repo_root,
                manifest=analyzer_manifest,
            )
            if extapi is not None:
                command.append(f"-extapi={extapi}")
            command.extend(["-print-fp", str(external_input)])
            completed = run_command(command, cwd=repo_root, timeout=timeout, check=False)
            observations = parse_svf_output(completed.stdout)
            report = canonicalize_external_report(
                inventory=inventory,
                observations=observations,
                candidate=external.label,
                adapter="svf",
            )
        elif external.label.startswith("phasar"):
            ll_path = _llvm_ir_for_external(
                external_input=external_input,
                linked_bc=linked_bc,
                llvm_dis=llvm_dis,
                manifest=analyzer_manifest,
                external=external,
                out_dir=out_dir,
                fixture=fixture,
                timeout=timeout,
                repo_root=repo_root,
            )
            phasar_dir = out_dir / f"{fixture.label}.{external.label}.phasar"
            phasar_dir.mkdir(parents=True, exist_ok=True)
            command = [
                str(tool),
                "--module",
                str(ll_path),
                f"--entry-points={fixture.entry_point}",
                "--call-graph-analysis=vta",
                "--emit-cg-as-json",
                "--out",
                str(phasar_dir),
                "--silent",
            ]
            completed = run_command(command, cwd=phasar_dir, timeout=timeout, check=False)
            observations = parse_phasar_output(completed.stdout)
            for callgraph_json in phasar_dir.rglob("psr-cg.json"):
                try:
                    observations.extend(
                        parse_phasar_callgraph_json(json.loads(callgraph_json.read_text()))
                    )
                except json.JSONDecodeError as exc:
                    raise CompareError(f"malformed PhASAR call graph JSON: {callgraph_json}") from exc
            results_json = phasar_dir / "results.json"
            if results_json.exists():
                try:
                    observations.extend(parse_phasar_results(json.loads(results_json.read_text())))
                except json.JSONDecodeError as exc:
                    raise CompareError(f"malformed PhASAR results.json: {results_json}") from exc
            report = canonicalize_external_report(
                inventory=inventory,
                observations=observations,
                candidate=external.label,
                adapter="phasar",
            )
        else:
            raise CompareError(
                f"cannot infer adapter for external candidate '{external.label}'; "
                "use labels starting with svf/phasar or json:/path/to/report"
            )
    except CompareError as exc:
        base.update(
            {
                "status": "failed",
                "error": str(exc),
                "command": [],
                "wall_ms": (time.monotonic() - start) * 1000.0,
            }
        )
        return base

    wall_ms = (time.monotonic() - start) * 1000.0
    report_path = out_dir / f"{fixture.label}.{external.label}.devirt.json"
    report = annotate_report_with_oracle(report, fixture=fixture.label)
    report_path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    base.update(
        {
            "command": command,
            "returncode": completed.returncode,
            "wall_ms": wall_ms,
            "report_path": str(report_path),
        }
    )
    if completed.returncode != 0:
        base.update({"status": "failed", "error": _error_tail(completed.stdout)})
        return base
    base.update({"status": "ok", "report": report, "metrics": devirt_metrics(report)})
    return base


def rank_candidates(records: list[dict[str, Any]]) -> list[dict[str, Any]]:
    grouped: dict[str, list[dict[str, Any]]] = {}
    for record in records:
        grouped.setdefault(str(record["candidate"]), []).append(record)

    def metric(record: dict[str, Any], name: str) -> int | float:
        return record.get("metrics", {}).get(name, 0)

    ranking: list[dict[str, Any]] = []
    for candidate, candidate_records in grouped.items():
        failures = [record for record in candidate_records if record["status"] != "ok"]
        ok_records = [record for record in candidate_records if record["status"] == "ok"]
        aggregate = {
            "total_callsites": sum(int(metric(record, "total_callsites")) for record in ok_records),
            "complete_callsites": sum(
                int(metric(record, "complete_callsites")) for record in ok_records
            ),
            "incomplete_callsites": sum(
                int(metric(record, "incomplete_callsites")) for record in ok_records
            ),
            "fallback_callsites": sum(
                int(metric(record, "fallback_callsites")) for record in ok_records
            ),
            "singleton_callsites": sum(
                int(metric(record, "singleton_callsites")) for record in ok_records
            ),
            "target_total": sum(int(metric(record, "target_total")) for record in ok_records),
            "complete_target_total": sum(
                int(metric(record, "complete_target_total")) for record in ok_records
            ),
            "fallback_target_total": sum(
                int(metric(record, "fallback_target_total")) for record in ok_records
            ),
            "max_target_count": max(
                (int(metric(record, "max_target_count")) for record in ok_records),
                default=0,
            ),
            "oracle_callsites": sum(
                int(metric(record, "oracle_callsites")) for record in ok_records
            ),
            "oracle_sound_callsites": sum(
                int(metric(record, "oracle_sound_callsites")) for record in ok_records
            ),
            "oracle_exact_callsites": sum(
                int(metric(record, "oracle_exact_callsites")) for record in ok_records
            ),
            "oracle_unsound_callsites": sum(
                int(metric(record, "oracle_unsound_callsites")) for record in ok_records
            ),
            "oracle_missing_target_total": sum(
                int(metric(record, "oracle_missing_target_total")) for record in ok_records
            ),
            "oracle_spurious_target_total": sum(
                int(metric(record, "oracle_spurious_target_total")) for record in ok_records
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
            -item["metrics"]["oracle_sound_callsites"],
            -item["metrics"]["oracle_exact_callsites"],
            item["metrics"]["oracle_missing_target_total"],
            item["metrics"]["oracle_spurious_target_total"],
            -item["metrics"]["complete_callsites"],
            -item["metrics"]["singleton_callsites"],
            item["metrics"]["fallback_callsites"],
            item["metrics"]["incomplete_callsites"],
            item["metrics"]["complete_target_total"],
            item["metrics"]["max_target_count"],
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
    llvm_dis: Path | None,
    fixtures: list[Fixture],
    candidates: list[Candidate],
    external_candidates: list[ExternalCandidate],
    analyzer_manifest: dict[str, Any] | None,
    external_inputs: dict[tuple[str, str], Path],
    records: list[dict[str, Any]],
) -> dict[str, Any]:
    return {
        "schema_version": SCHEMA_VERSION,
        "repo_root": str(repo_root),
        "tools": {
            "llvm2bpl": str(llvm2bpl),
            "clang": str(clang),
            "llvm_link": str(llvm_link),
            "llvm_dis": str(llvm_dis) if llvm_dis else None,
        },
        "ranking_rule": (
            "fewer failed fixtures; when expected-target oracles are available, "
            "more sound/exact oracle callsites and fewer missing/spurious oracle "
            "targets; then more resolved/singleton callsites, fewer fallback/"
            "incomplete callsites, smaller complete target sets, and less wall time"
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
            {"label": candidate.label, "tools": list(candidate.tools)}
            for candidate in external_candidates
        ],
        "analyzer_manifest": (
            {
                "path": analyzer_manifest.get("manifest_path"),
                "analyzers": analyzer_manifest.get("analyzers", {}),
            }
            if analyzer_manifest
            else None
        ),
        "external_inputs": [
            {"candidate": candidate, "fixture": fixture, "path": str(path)}
            for (candidate, fixture), path in sorted(external_inputs.items())
        ],
        "ranking": rank_candidates(records),
        "records": records,
    }


def _cell(record: dict[str, Any], callsite_id: str) -> str:
    if record["status"] != "ok":
        return "failed"
    for call in record["report"].get("callsites", []):
        if call.get("callsite_id") == callsite_id:
            prefix = "C" if call.get("complete") else "I"
            targets = ",".join(call.get("targets", []))
            if len(targets) > 60:
                targets = targets[:57] + "..."
            oracle = ""
            if "expected_targets" in call:
                if call.get("oracle_exact") is True:
                    oracle = " exact"
                elif call.get("oracle_sound") is True:
                    oracle = f" sound +{len(call.get('spurious_targets', []))}"
                else:
                    oracle = (
                        f" miss {len(call.get('missing_targets', []))}"
                        f" +{len(call.get('spurious_targets', []))}"
                    )
            return f"{prefix}:{call.get('target_count', 0)}{oracle} {targets}".strip()
    return ""


def write_markdown(summary: dict[str, Any], path: Path) -> None:
    has_oracle = any(
        item["metrics"].get("oracle_callsites", 0) > 0 for item in summary["ranking"]
    )
    lines = [
        "# SMACK Devirtualization Comparison",
        "",
        f"Ranking rule: {summary['ranking_rule']}.",
        "",
        "## Ranking",
        "",
    ]
    if has_oracle:
        lines.extend(
            [
                (
                    "| Rank | Candidate | OK | Fail | Oracle Sound | Oracle Exact | "
                    "Missing | Spurious | Complete | Singleton | Fallback | "
                    "Incomplete | Targets | Max Targets |"
                ),
                (
                    "| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: | "
                    "---: | ---: | ---: | ---: | ---: | ---: |"
                ),
            ]
        )
    else:
        lines.extend(
            [
                (
                    "| Rank | Candidate | OK | Fail | Complete | Singleton | Fallback | "
                    "Incomplete | Targets | Max Targets |"
                ),
                "| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |",
            ]
        )
    for item in summary["ranking"]:
        metrics = item["metrics"]
        if has_oracle:
            lines.append(
                "| {rank} | `{candidate}` | {ok_count} | {failure_count} | "
                "{oracle_sound_callsites}/{oracle_callsites} | "
                "{oracle_exact_callsites}/{oracle_callsites} | "
                "{oracle_missing_target_total} | {oracle_spurious_target_total} | "
                "{complete_callsites} | {singleton_callsites} | {fallback_callsites} | "
                "{incomplete_callsites} | {complete_target_total} | {max_target_count} |".format(
                    rank=item["rank"],
                    candidate=item["candidate"],
                    ok_count=item["ok_count"],
                    failure_count=item["failure_count"],
                    oracle_sound_callsites=metrics["oracle_sound_callsites"],
                    oracle_callsites=metrics["oracle_callsites"],
                    oracle_exact_callsites=metrics["oracle_exact_callsites"],
                    oracle_missing_target_total=metrics["oracle_missing_target_total"],
                    oracle_spurious_target_total=metrics["oracle_spurious_target_total"],
                    complete_callsites=metrics["complete_callsites"],
                    singleton_callsites=metrics["singleton_callsites"],
                    fallback_callsites=metrics["fallback_callsites"],
                    incomplete_callsites=metrics["incomplete_callsites"],
                    complete_target_total=metrics["complete_target_total"],
                    max_target_count=metrics["max_target_count"],
                )
            )
        else:
            lines.append(
                "| {rank} | `{candidate}` | {ok_count} | {failure_count} | "
                "{complete_callsites} | {singleton_callsites} | {fallback_callsites} | "
                "{incomplete_callsites} | {complete_target_total} | {max_target_count} |".format(
                    rank=item["rank"],
                    candidate=item["candidate"],
                    ok_count=item["ok_count"],
                    failure_count=item["failure_count"],
                    complete_callsites=metrics["complete_callsites"],
                    singleton_callsites=metrics["singleton_callsites"],
                    fallback_callsites=metrics["fallback_callsites"],
                    incomplete_callsites=metrics["incomplete_callsites"],
                    complete_target_total=metrics["complete_target_total"],
                    max_target_count=metrics["max_target_count"],
                )
            )

    ok_records = [record for record in summary["records"] if record["status"] == "ok"]
    candidates: list[str] = []
    for record in summary["records"]:
        candidate = str(record["candidate"])
        if candidate not in candidates:
            candidates.append(candidate)
    first_by_fixture: dict[str, dict[str, Any]] = {}
    for record in ok_records:
        first_by_fixture.setdefault(record["fixture"], record)

    if ok_records:
        lines.extend(["", "## Per-Callsite Comparison", ""])
        header = "| Fixture | Callsite | Function | " + " | ".join(
            f"`{candidate}`" for candidate in candidates
        ) + " |"
        sep = "| --- | --- | --- | " + " | ".join("---" for _ in candidates) + " |"
        lines.extend([header, sep])
        for fixture, record in first_by_fixture.items():
            for call in record["report"].get("callsites", []):
                callsite_id = str(call.get("callsite_id", ""))
                by_candidate = {
                    str(candidate_record["candidate"]): candidate_record
                    for candidate_record in summary["records"]
                    if candidate_record["fixture"] == fixture
                }
                lines.append(
                    "| `{fixture}` | `{callsite}` | `{function}` | {cells} |".format(
                        fixture=fixture,
                        callsite=callsite_id,
                        function=call.get("function", ""),
                        cells=" | ".join(
                            _cell(by_candidate[candidate], callsite_id)
                            if candidate in by_candidate
                            else ""
                            for candidate in candidates
                        ),
                    )
                )

    lines.extend(["", "## Failed Runs", ""])
    failed = [record for record in summary["records"] if record["status"] != "ok"]
    if failed:
        for record in failed:
            lines.extend(
                [
                    f"- `{record['candidate']}` on `{record['fixture']}` failed.",
                    "",
                    "```text",
                    str(record.get("error", "")),
                    "```",
                    "",
                ]
            )
    else:
        lines.append("No candidate runs failed.")

    path.write_text("\n".join(lines) + "\n")


def run_comparison(
    *,
    repo_root: Path,
    out_dir: Path,
    llvm2bpl: Path,
    clang: Path,
    llvm_link: Path,
    llvm_dis: Path | None,
    fixtures: list[Fixture],
    candidates: list[Candidate],
    external_candidates: list[ExternalCandidate],
    analyzer_manifest: dict[str, Any] | None,
    external_inputs: dict[tuple[str, str], Path],
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
        fixture_records: list[dict[str, Any]] = []
        for candidate in candidates:
            record = _run_smack_candidate(
                llvm2bpl=llvm2bpl,
                linked_bc=linked_bc,
                fixture=fixture,
                candidate=candidate,
                repo_root=repo_root,
                out_dir=out_dir,
                timeout=timeout,
            )
            fixture_records.append(record)
            records.append(record)

        inventory = next(
            (record["report"] for record in fixture_records if record["status"] == "ok"),
            None,
        )
        if external_candidates and inventory is None:
            raise CompareError(f"cannot run external analyzers without callsite inventory: {fixture.label}")
        if inventory is not None:
            for external in external_candidates:
                records.append(
                    _run_external_candidate(
                        linked_bc=linked_bc,
                        fixture=fixture,
                        external=external,
                        inventory=inventory,
                        repo_root=repo_root,
                        out_dir=out_dir,
                        llvm_dis=llvm_dis,
                        analyzer_manifest=analyzer_manifest,
                        external_inputs=external_inputs,
                        timeout=timeout,
                    )
                )

    if not any(record["status"] == "ok" for record in records):
        raise CompareError("all devirtualization candidate runs failed")

    return build_summary(
        repo_root=repo_root,
        llvm2bpl=llvm2bpl,
        clang=clang,
        llvm_link=llvm_link,
        llvm_dis=llvm_dis,
        fixtures=fixtures,
        candidates=candidates,
        external_candidates=external_candidates,
        analyzer_manifest=analyzer_manifest,
        external_inputs=external_inputs,
        records=records,
    )


def make_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=_repo_root())
    parser.add_argument("--out-dir", type=Path, default=Path("build/devirt-compare"))
    parser.add_argument("--llvm2bpl")
    parser.add_argument("--clang")
    parser.add_argument("--llvm-link")
    parser.add_argument("--llvm-dis")
    parser.add_argument("--timeout", type=int, default=180)
    parser.add_argument(
        "--analyzer-manifest",
        type=Path,
        default=None,
        help="local analyzer manifest from tools/install_devirt_analyzers.py",
    )
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
        help="SMACK/llvm2bpl candidate flags; may be repeated",
    )
    parser.add_argument(
        "--external-candidate",
        action="append",
        default=[],
        metavar="NAME=TOOL[,TOOL]",
        help=(
            "external analyzer candidate; labels starting with svf or phasar use "
            "built-in adapters, json:/path loads a canonical report"
        ),
    )
    parser.add_argument(
        "--no-default-external",
        action="store_true",
        help="skip default hard external candidates: SVF and PhASAR",
    )
    parser.add_argument(
        "--allow-external-failures",
        action="store_true",
        help="write comparison output and exit 0 even if external analyzers fail",
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
        "--bearssl-bc",
        type=Path,
        default=None,
        help="prebuilt BearSSL LLVM bitcode; equivalent to --bc-fixture bearssl=PATH:bearssl_devirt_entry",
    )
    parser.add_argument(
        "--external-input",
        action="append",
        default=[],
        metavar="CANDIDATE:FIXTURE=PATH",
        help=(
            "override bitcode/IR input for an external analyzer; CANDIDATE may be "
            "svf, phasar, a full candidate label, or *"
        ),
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
        analyzer_manifest = (
            load_analyzer_manifest(args.analyzer_manifest, repo_root=repo_root)
            if args.analyzer_manifest
            else None
        )
        llvm_dis: Path | None
        if args.llvm_dis or not args.no_default_external or args.external_candidate:
            llvm_dis = resolve_tool(args.llvm_dis, "llvm-dis", repo_root=repo_root)
        else:
            llvm_dis = None

        candidates = [parse_candidate(spec) for spec in (args.candidate or DEFAULT_CANDIDATES)]
        fixture_specs = list(args.fixture or [])
        bc_fixture_specs = list(args.bc_fixture or [])
        if args.bearssl_bc:
            bc_fixture_specs.append(f"bearssl={args.bearssl_bc}:bearssl_devirt_entry")
        if not fixture_specs and not bc_fixture_specs:
            fixture_specs = list(DEFAULT_FIXTURES)
        fixtures = [parse_fixture(spec) for spec in fixture_specs]
        fixtures.extend(
            parse_bc_fixture(spec, link_runtime=not args.no_link_runtime)
            for spec in bc_fixture_specs
        )

        external_specs = list(args.external_candidate or [])
        if not args.no_default_external:
            external_specs.extend(DEFAULT_EXTERNAL_CANDIDATES)
        external_candidates = [parse_external_candidate(spec) for spec in external_specs]
        external_inputs = {
            (external_input.candidate, external_input.fixture): external_input.path
            for external_input in (
                parse_external_input(spec) for spec in args.external_input
            )
        }

        summary = run_comparison(
            repo_root=repo_root,
            out_dir=out_dir,
            llvm2bpl=llvm2bpl,
            clang=clang,
            llvm_link=llvm_link,
            llvm_dis=llvm_dis,
            fixtures=fixtures,
            candidates=candidates,
            external_candidates=external_candidates,
            analyzer_manifest=analyzer_manifest,
            external_inputs=external_inputs,
            timeout=args.timeout,
        )
    except CompareError as exc:
        parser.error(str(exc))

    json_path = out_dir / "devirt-comparison.json"
    md_path = out_dir / "devirt-comparison.md"
    json_path.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    write_markdown(summary, md_path)
    print(f"wrote {json_path}")
    print(f"wrote {md_path}")
    best = summary["ranking"][0]
    print(f"best candidate: {best['candidate']} (rank {best['rank']})")
    external_failures = [
        record
        for record in summary["records"]
        if record.get("kind") == "external" and record.get("status") != "ok"
    ]
    if external_failures and not args.allow_external_failures:
        failed = ", ".join(
            f"{record['candidate']} on {record['fixture']}" for record in external_failures
        )
        print(
            "external analyzer comparison failed: "
            f"{failed}; rerun with --allow-external-failures to keep this as a report-only failure",
            file=sys.stderr,
        )
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

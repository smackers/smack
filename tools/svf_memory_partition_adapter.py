#!/usr/bin/env python3
"""Build a conservative SMACK memory-partition oracle from SVF MemorySSA.

The adapter consumes the textual LLVM IR produced by `llvm2bpl -ll` and SVF's
`wpa -ander -svfg -dump-mssa` output. It records MemorySSA region identifiers
for loads and stores only when the dumped LLVM instruction text matches the
pre-BPL module instruction text exactly after removing SVF's source-location
suffixes.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import tempfile
from collections.abc import Iterable
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

SCHEMA_VERSION = 3
PRODUCER = "svf-memory-partition-adapter"
FNV_OFFSET = 14695981039346656037
FNV_PRIME = 1099511628211
FNV_MASK = (1 << 64) - 1

FUNCTION_RE = re.compile(r"^\s*define\b.*@(?:(\"(?:\\.|[^\"])+\")|([^\s(]+))\s*\(")
DECLARE_RE = re.compile(r"^\s*declare\b.*@(?:(\"(?:\\.|[^\"])+\")|([^\s(]+))\s*\(")
FUNCTION_DUMP_RE = re.compile(r"^=+FUNCTION:\s*(.*?)=+$")
MR_RE = re.compile(r"MR_(\d+)V_\d+")
SOURCE_LOC_RE = re.compile(r"\s+\{\s*\"ln\":.*$")
CALL_ICFG_RE = re.compile(r"\s+CallICFGNode:.*$")
METADATA_ATTACHMENT_RE = re.compile(r", ![-A-Za-z0-9_.]+ !\d+")
DIRECT_CALLEE_RE = re.compile(r"@(?:(\"(?:\\.|[^\"])+\")|([^\s(]+))\s*\(")
STRUCT_GEP_I64_FIELD_RE = re.compile(
    r"(getelementptr(?:\s+inbounds)?\s+%[^,]*struct[^,]*,\s+ptr\s+[^,]+,"
    r"\s+i\d+\s+[^,]+,\s*)i64(\s+-?\d+)"
)
NAMED_STRUCT_TYPE_RE = re.compile(
    r"^\s*(%[-A-Za-z$._0-9]+)\s*=\s*type\s*\{\s*(.*?)\s*\}\s*$"
)
NAMED_STRUCT_GEP_RE = re.compile(
    r"(?P<prefix>getelementptr(?:\s+(?:inbounds|nuw|nusw))*\s+"
    r"(?P<source_type>%[-A-Za-z$._0-9]+),\s+ptr\s+[^,]+)"
    r"(?P<indices>(?:,\s+i\d+\s+-?\d+)+)"
    r"(?P<suffix>(?:,\s*![^,]+ !\d+.*)?)$"
)
GEP_INDEX_RE = re.compile(r",\s+i\d+\s+-?\d+")
LABEL_RE = re.compile(r"^([A-Za-z$._][-A-Za-z$._0-9]*|\d+):(?:\s*;.*)?$")
BRANCH_LABEL_RE = re.compile(r"label\s+%([A-Za-z$._][-A-Za-z$._0-9]*|\d+)")
PRINT_FP_CALLSITE_RE = re.compile(r"^\s*CallSite:\s+CallICFGNode\d+\s+\{fun:\s*([^\s{]+)")


class AdapterError(RuntimeError):
    """Raised when an SVF oracle cannot be generated."""


@dataclass
class EffectRegions:
    ref_regions: set[str] = field(default_factory=set)
    mod_regions: set[str] = field(default_factory=set)
    complete: bool = True


@dataclass
class CallInfo:
    function: str
    instruction: str
    key: str
    target: str | None
    indirect: bool
    block: str


@dataclass
class InstructionInfo:
    function: str
    block: str
    instruction: str
    key: str
    kind: str
    target: str | None = None
    indirect: bool = False


@dataclass
class BasicBlockInfo:
    label: str
    instructions: list[InstructionInfo] = field(default_factory=list)
    successors: list[str] = field(default_factory=list)
    loop_latch_successors: list[str] = field(default_factory=list)


@dataclass
class FunctionIrInfo:
    name: str
    blocks: dict[str, BasicBlockInfo] = field(default_factory=dict)
    order: list[str] = field(default_factory=list)


@dataclass
class ModuleIrInfo:
    functions: dict[str, FunctionIrInfo] = field(default_factory=dict)
    access_keys: list[str] = field(default_factory=list)
    call_infos: list[CallInfo] = field(default_factory=list)


@dataclass
class ParsedSvfDump:
    access_regions: dict[str, set[str]] = field(default_factory=dict)
    callsite_effects: dict[str, EffectRegions] = field(default_factory=dict)
    function_effects: dict[str, EffectRegions] = field(default_factory=dict)
    seen_functions: set[str] = field(default_factory=set)


def _decode_llvm_name(text: str) -> str:
    if not text.startswith('"'):
        return text
    body = text[1:-1]

    def repl(match: re.Match[str]) -> str:
        return chr(int(match.group(1), 16))

    return re.sub(r"\\([0-9A-Fa-f]{2})", repl, body).replace(r"\"", '"').replace(r"\\", "\\")


def normalize_ir_instruction(line: str) -> str:
    text = line.strip()
    text = SOURCE_LOC_RE.sub("", text)
    text = CALL_ICFG_RE.sub("", text)
    text = METADATA_ATTACHMENT_RE.sub("", text)
    return text.rstrip()


def is_load_instruction(text: str) -> bool:
    return " = load " in text


def is_store_instruction(text: str) -> bool:
    return text.startswith("store ")


def is_call_instruction(text: str) -> bool:
    return (
        text.startswith("call ")
        or " = call " in text
        or text.startswith("invoke ")
        or " = invoke " in text
    )


def fnv1a64(values: Iterable[str]) -> str:
    value = FNV_OFFSET
    for item in values:
        for byte in item.encode():
            value ^= byte
            value = (value * FNV_PRIME) & FNV_MASK
        value ^= ord("\n")
        value = (value * FNV_PRIME) & FNV_MASK
    return f"{value:016x}"


def _split_top_level_fields(body: str) -> list[str]:
    fields: list[str] = []
    start = 0
    depth = 0
    pairs = {"{": "}", "[": "]", "(": ")", "<": ">"}
    closing = set(pairs.values())

    for index, char in enumerate(body):
        if char in pairs:
            depth += 1
            continue
        if char in closing:
            depth = max(0, depth - 1)
            continue
        if char == "," and depth == 0:
            fields.append(body[start:index].strip())
            start = index + 1

    tail = body[start:].strip()
    if tail:
        fields.append(tail)
    return fields


def _named_struct_fields(ll_text: str) -> dict[str, list[str]]:
    fields: dict[str, list[str]] = {}
    for line in ll_text.splitlines():
        match = NAMED_STRUCT_TYPE_RE.match(line)
        if match:
            fields[match.group(1)] = _split_top_level_fields(match.group(2))
    return fields


def _index_value(index_text: str) -> int | None:
    try:
        return int(index_text.rsplit(maxsplit=1)[1])
    except (IndexError, ValueError):
        return None


def _truncate_invalid_named_struct_geps(
    ll_text: str, named_fields: dict[str, list[str]]
) -> tuple[str, int]:
    changed = 0
    lines: list[str] = []

    for line in ll_text.splitlines(keepends=True):
        newline = ""
        if line.endswith("\n"):
            line, newline = line[:-1], "\n"

        match = NAMED_STRUCT_GEP_RE.search(line)
        if not match:
            lines.append(line + newline)
            continue

        current_type = match.group("source_type")
        indices = GEP_INDEX_RE.findall(match.group("indices"))
        kept_indices: list[str] = []
        truncate = False
        for index, index_text in enumerate(indices):
            kept_indices.append(index_text)
            if index == 0:
                continue

            field_types = named_fields.get(current_type)
            if field_types is None:
                break

            field_index = _index_value(index_text)
            if field_index is None or field_index < 0 or field_index >= len(field_types):
                kept_indices.pop()
                truncate = True
                break

            current_type = field_types[field_index]

        if truncate:
            line = (
                line[: match.start()]
                + match.group("prefix")
                + "".join(kept_indices)
                + match.group("suffix")
            )
            changed += 1

        lines.append(line + newline)

    return "".join(lines), changed


def sanitize_ir_for_svf(ll_text: str) -> tuple[str, int]:
    """Repair textual IR forms LLVM accepts in-memory but SVF rejects.

    Some SMACK-normalized typed-struct GEPs have an `i64` struct-field index in
    textual IR. LLVM's assembler and SVF require struct-field indices to be
    `i32`. The adapter only keys loads/stores, so rewriting those GEP index
    types for SVF input does not change oracle keys or module fingerprints.

    Older typed-struct lowering can also leave C-union member accesses as GEPs
    through non-existent fields of LLVM's single-field union representation. For
    SVF input, truncate those GEPs to the last valid aggregate field. That is
    conservative for region splitting because it can only make the pointer
    analysis see a coarser location for that access path.
    """

    sanitized, i64_count = STRUCT_GEP_I64_FIELD_RE.subn(r"\1i32\2", ll_text)
    sanitized, truncated_count = _truncate_invalid_named_struct_geps(
        sanitized, _named_struct_fields(sanitized)
    )
    return sanitized, i64_count + truncated_count


def _block_label(text: str) -> str:
    return text[1:] if text.startswith("%") else text


def _ensure_block(function: FunctionIrInfo, label: str) -> BasicBlockInfo:
    if label not in function.blocks:
        function.blocks[label] = BasicBlockInfo(label=label)
        function.order.append(label)
    return function.blocks[label]


def parse_module_ir(ll_text: str) -> ModuleIrInfo:
    module = ModuleIrInfo()
    current_function: FunctionIrInfo | None = None
    current_block: BasicBlockInfo | None = None

    for line in ll_text.splitlines():
        match = FUNCTION_RE.match(line)
        if match:
            name = _decode_llvm_name(match.group(1) or match.group(2) or "")
            current_function = FunctionIrInfo(name=name)
            module.functions[name] = current_function
            current_block = _ensure_block(current_function, "entry")
            continue

        if current_function is None:
            continue

        if line.startswith("}"):
            current_function = None
            current_block = None
            continue

        label_match = LABEL_RE.match(line.strip())
        if label_match:
            current_block = _ensure_block(
                current_function, _block_label(label_match.group(1))
            )
            continue

        if current_block is None:
            current_block = _ensure_block(current_function, "entry")

        raw_instruction = line.strip()
        instruction = normalize_ir_instruction(line)
        if not instruction:
            continue

        successors = [_block_label(label) for label in BRANCH_LABEL_RE.findall(instruction)]
        if successors:
            current_block.successors = successors
            if "llvm.loop" in raw_instruction:
                current_block.loop_latch_successors = successors

        kind: str | None = None
        target: str | None = None
        indirect = False
        if is_load_instruction(instruction):
            kind = "load"
        elif is_store_instruction(instruction):
            kind = "store"
        elif is_call_instruction(instruction):
            kind = "call"
            target = _direct_callee(instruction)
            indirect = target is None

        if kind is None:
            continue

        key = f"{current_function.name}\t{instruction}"
        info = InstructionInfo(
            function=current_function.name,
            block=current_block.label,
            instruction=instruction,
            key=key,
            kind=kind,
            target=target,
            indirect=indirect,
        )
        current_block.instructions.append(info)
        if kind in {"load", "store"}:
            module.access_keys.append(key)
        if kind == "call":
            module.call_infos.append(
                CallInfo(
                    function=current_function.name,
                    instruction=instruction,
                    key=key,
                    target=target,
                    indirect=indirect,
                    block=current_block.label,
                )
            )

    return module


def iter_module_access_keys(ll_text: str) -> list[str]:
    return parse_module_ir(ll_text).access_keys


def iter_module_function_names(ll_text: str) -> list[str]:
    names: list[str] = []
    for line in ll_text.splitlines():
        match = FUNCTION_RE.match(line)
        if match:
            names.append(_decode_llvm_name(match.group(1) or match.group(2) or ""))
    return names


def iter_module_declarations(ll_text: str) -> set[str]:
    names: set[str] = set()
    for line in ll_text.splitlines():
        match = DECLARE_RE.match(line)
        if match:
            names.add(_decode_llvm_name(match.group(1) or match.group(2) or ""))
    return names


def _direct_callee(instruction: str) -> str | None:
    match = DIRECT_CALLEE_RE.search(instruction)
    if not match:
        return None
    return _decode_llvm_name(match.group(1) or match.group(2) or "")


def iter_module_call_infos(ll_text: str) -> list[CallInfo]:
    return parse_module_ir(ll_text).call_infos


def _known_modeled_external(name: str) -> bool:
    return (
        name.startswith("llvm.dbg.")
        or name.startswith("llvm.lifetime.")
        or name == "llvm.assume"
        or name.startswith("__VERIFIER_nondet")
        or name.startswith("__SMACK_nondet")
        or name in {"malloc", "free"}
    )


def _region_ids(line: str) -> list[str]:
    return [f"MR_{region_id}" for region_id in MR_RE.findall(line)]


def _add_regions(access_regions: dict[str, set[str]], key: str, regions: Iterable[str]) -> None:
    region_set = access_regions.setdefault(key, set())
    region_set.update(regions)


def _effect(parsed: ParsedSvfDump, function: str) -> EffectRegions:
    return parsed.function_effects.setdefault(function, EffectRegions())


def _callsite_effect(parsed: ParsedSvfDump, key: str) -> EffectRegions:
    return parsed.callsite_effects.setdefault(key, EffectRegions())


def parse_svf_dump_full(output: str) -> ParsedSvfDump:
    parsed = ParsedSvfDump()
    current_function: str | None = None
    pending_load_regions: list[str] = []
    pending_call_ref_regions: list[str] = []
    waiting_for_load = False
    waiting_for_store = False
    waiting_for_call = False
    current_store_key: str | None = None
    current_call_key: str | None = None

    for raw_line in output.splitlines():
        line = raw_line.rstrip()
        function_match = FUNCTION_DUMP_RE.match(line)
        if function_match:
            current_function = function_match.group(1)
            parsed.seen_functions.add(current_function)
            _effect(parsed, current_function)
            pending_load_regions = []
            pending_call_ref_regions = []
            waiting_for_load = False
            waiting_for_store = False
            waiting_for_call = False
            current_store_key = None
            current_call_key = None
            continue

        if current_function is None:
            continue

        if line.startswith("LDMU("):
            regions = _region_ids(line)
            pending_load_regions.extend(regions)
            _effect(parsed, current_function).ref_regions.update(regions)
            continue

        if "CALMU(" in line:
            regions = _region_ids(line)
            pending_call_ref_regions.extend(regions)
            _effect(parsed, current_function).ref_regions.update(regions)
            continue

        if "LoadStmt:" in line:
            waiting_for_load = True
            waiting_for_store = False
            waiting_for_call = False
            current_store_key = None
            current_call_key = None
            continue

        if "StoreStmt:" in line:
            waiting_for_store = True
            waiting_for_load = False
            waiting_for_call = False
            current_store_key = None
            current_call_key = None
            continue

        if line.startswith("CallICFGNode"):
            waiting_for_call = True
            waiting_for_load = False
            waiting_for_store = False
            current_store_key = None
            current_call_key = None
            continue

        if "STCHI(" in line:
            regions = _region_ids(line)
            _effect(parsed, current_function).mod_regions.update(regions)
            if current_store_key is not None:
                _add_regions(parsed.access_regions, current_store_key, regions)
            continue

        if "CALCHI(" in line:
            regions = _region_ids(line)
            _effect(parsed, current_function).mod_regions.update(regions)
            if current_call_key is not None:
                _callsite_effect(parsed, current_call_key).mod_regions.update(regions)
            continue

        instruction = normalize_ir_instruction(line)
        if waiting_for_load and is_load_instruction(instruction):
            key = f"{current_function}\t{instruction}"
            _add_regions(parsed.access_regions, key, pending_load_regions)
            pending_load_regions = []
            waiting_for_load = False
            continue

        if waiting_for_store and is_store_instruction(instruction):
            current_store_key = f"{current_function}\t{instruction}"
            waiting_for_store = False
            continue

        if waiting_for_call and is_call_instruction(instruction):
            current_call_key = f"{current_function}\t{instruction}"
            _callsite_effect(parsed, current_call_key).ref_regions.update(
                pending_call_ref_regions
            )
            pending_call_ref_regions = []
            waiting_for_call = False
            continue

        if line.startswith("CallICFGNode") or line.endswith("Stmt:"):
            waiting_for_load = False
            waiting_for_store = False
            waiting_for_call = False
            current_store_key = None
            current_call_key = None
            pending_load_regions = []
            pending_call_ref_regions = []

    return parsed


def parse_svf_dump(output: str) -> dict[str, set[str]]:
    return parse_svf_dump_full(output).access_regions


def _effect_to_json(effect: EffectRegions) -> dict[str, Any]:
    return {
        "ref_regions": sorted(effect.ref_regions),
        "mod_regions": sorted(effect.mod_regions),
        "complete": effect.complete,
    }


def _reverse_predecessors(function: FunctionIrInfo) -> dict[str, set[str]]:
    predecessors: dict[str, set[str]] = {label: set() for label in function.blocks}
    for label, block in function.blocks.items():
        for successor in block.successors:
            predecessors.setdefault(successor, set()).add(label)
    return predecessors


def _natural_loop_blocks(
    function: FunctionIrInfo, header: str, latch: str
) -> set[str]:
    predecessors = _reverse_predecessors(function)
    blocks = {header, latch}
    work = [latch]
    while work:
        label = work.pop()
        for pred in predecessors.get(label, set()):
            if pred in blocks:
                continue
            blocks.add(pred)
            if pred != header:
                work.append(pred)
    return blocks


def _loop_header_candidates(function: FunctionIrInfo) -> list[tuple[str, str, set[str]]]:
    candidates: list[tuple[str, str, set[str]]] = []
    for latch_label, block in function.blocks.items():
        for successor in block.loop_latch_successors:
            if successor not in function.blocks:
                continue
            candidates.append(
                (
                    successor,
                    latch_label,
                    _natural_loop_blocks(function, successor, latch_label),
                )
            )
    return candidates


def build_loop_effects(
    *,
    module_ir: ModuleIrInfo,
    matched_access_regions: dict[str, list[str]],
    callsite_effects: dict[str, dict[str, Any]],
    function_effects: dict[str, dict[str, Any]],
    module_declarations: set[str],
) -> dict[str, dict[str, Any]]:
    loop_effects: dict[str, dict[str, Any]] = {}
    for function in module_ir.functions.values():
        for header, _latch, block_labels in _loop_header_candidates(function):
            effect = EffectRegions()
            for label in block_labels:
                block = function.blocks.get(label)
                if block is None:
                    effect.complete = False
                    continue
                for instruction in block.instructions:
                    if instruction.kind == "load":
                        regions = matched_access_regions.get(instruction.key)
                        if regions:
                            effect.ref_regions.update(regions)
                        continue
                    if instruction.kind == "store":
                        regions = matched_access_regions.get(instruction.key)
                        if regions:
                            effect.mod_regions.update(regions)
                        else:
                            effect.complete = False
                        continue
                    if instruction.kind != "call":
                        continue

                    call_effect = callsite_effects.get(instruction.key)
                    if call_effect is not None:
                        effect.ref_regions.update(call_effect.get("ref_regions", []))
                        effect.mod_regions.update(call_effect.get("mod_regions", []))
                        effect.complete = effect.complete and bool(
                            call_effect.get("complete", False)
                        )
                        continue

                    target = instruction.target
                    if target is not None and _known_modeled_external(target):
                        continue

                    function_effect = function_effects.get(target or "")
                    if function_effect is not None:
                        effect.ref_regions.update(function_effect.get("ref_regions", []))
                        effect.mod_regions.update(function_effect.get("mod_regions", []))
                        effect.complete = effect.complete and bool(
                            function_effect.get("complete", False)
                        )
                        continue

                    if target in module_declarations or target is None:
                        effect.complete = False

            key = f"{function.name}\t{header}"
            value = _effect_to_json(effect)
            value["function"] = function.name
            value["header"] = header
            value["blocks"] = sorted(block_labels)
            loop_effects[key] = value
    return loop_effects


def parse_print_fp_targets(output: str, module_calls: list[CallInfo]) -> dict[str, dict[str, Any]]:
    call_by_instruction = {call.instruction: call for call in module_calls}
    targets: dict[str, dict[str, Any]] = {}
    current_key: str | None = None
    waiting_for_instruction = False
    waiting_for_targets = False

    for raw_line in output.splitlines():
        line = raw_line.rstrip()
        if PRINT_FP_CALLSITE_RE.match(line):
            current_key = None
            waiting_for_instruction = True
            waiting_for_targets = False
            continue

        if waiting_for_instruction:
            instruction = normalize_ir_instruction(line)
            if is_call_instruction(instruction):
                call = call_by_instruction.get(instruction)
                if call is not None:
                    current_key = call.key
                    targets[current_key] = {"targets": [], "complete": True}
                waiting_for_instruction = False
                waiting_for_targets = "with Targets:" in line
            continue

        if current_key is None:
            continue

        if "with Targets:" in line:
            waiting_for_targets = True
            continue

        if waiting_for_targets:
            target = line.strip()
            if not target:
                continue
            if target.startswith("*") or target.startswith("="):
                waiting_for_targets = False
                current_key = None
                continue
            if target not in targets[current_key]["targets"]:
                targets[current_key]["targets"].append(target)

    for value in targets.values():
        value["targets"] = sorted(value["targets"])
        if not value["targets"]:
            value["complete"] = False
    return targets


def build_diagnostics(
    *,
    loop_effects: dict[str, dict[str, Any]],
    indirect_call_targets: dict[str, dict[str, Any]],
    loop_diagnostics: bool,
    saber_diagnostics: bool,
    mta_diagnostics: bool,
) -> dict[str, Any]:
    diagnostics: dict[str, Any] = {}
    if loop_diagnostics:
        diagnostics["loops"] = {
            "loop_count": len(loop_effects),
            "complete_loop_count": sum(
                1 for effect in loop_effects.values() if effect.get("complete")
            ),
            "incomplete_loop_count": sum(
                1 for effect in loop_effects.values() if not effect.get("complete")
            ),
        }
    if indirect_call_targets:
        diagnostics["indirect_calls"] = {
            "callsite_count": len(indirect_call_targets),
            "complete_callsite_count": sum(
                1
                for target in indirect_call_targets.values()
                if target.get("complete")
            ),
        }
    if saber_diagnostics:
        diagnostics["saber"] = {"enabled": True, "findings": []}
    if mta_diagnostics:
        diagnostics["mta"] = {"enabled": True, "findings": []}
    return diagnostics


def build_oracle(
    *,
    ll_text: str,
    svf_output: str,
    analysis: str = "andersen",
    memory_partition: str = "intra-disjoint",
    collect_indirect_calls: bool = False,
    loop_diagnostics: bool = False,
    saber_diagnostics: bool = False,
    mta_diagnostics: bool = False,
) -> dict[str, Any]:
    module_ir = parse_module_ir(ll_text)
    module_keys = module_ir.access_keys
    module_key_set = set(module_keys)
    module_functions = iter_module_function_names(ll_text)
    module_declarations = iter_module_declarations(ll_text)
    module_calls = module_ir.call_infos
    module_call_keys = {call.key for call in module_calls}
    calls_by_function: dict[str, list[CallInfo]] = {}
    for call in module_calls:
        calls_by_function.setdefault(call.function, []).append(call)

    parsed = parse_svf_dump_full(svf_output)
    svf_access_regions = parsed.access_regions
    matched = {
        key: sorted(regions)
        for key, regions in sorted(svf_access_regions.items())
        if key in module_key_set and regions
    }
    matched_callsite_effects: dict[str, dict[str, Any]] = {}
    call_by_key = {call.key: call for call in module_calls}
    for key, effect in sorted(parsed.callsite_effects.items()):
        if key not in module_call_keys:
            continue
        call = call_by_key[key]
        effect.complete = not (
            call.indirect
            or (
                call.target in module_declarations
                and call.target is not None
                and not _known_modeled_external(call.target)
            )
        )
        matched_callsite_effects[key] = _effect_to_json(effect)

    function_effects: dict[str, dict[str, Any]] = {}
    access_functions = {key.split("\t", 1)[0] for key in module_keys}
    for function in module_functions:
        effect = parsed.function_effects.get(function, EffectRegions())
        function_calls = calls_by_function.get(function, [])
        has_unknown_call = any(
            call.indirect
            or (
                call.target in module_declarations
                and call.target is not None
                and not _known_modeled_external(call.target)
            )
            for call in function_calls
        )
        has_memory_or_calls = function in access_functions or bool(function_calls)
        effect.complete = (
            not has_unknown_call
            and (function in parsed.seen_functions or not has_memory_or_calls)
        )
        function_effects[function] = _effect_to_json(effect)

    incomplete_function_count = sum(
        1 for effect in function_effects.values() if not effect["complete"]
    )
    loop_effects = build_loop_effects(
        module_ir=module_ir,
        matched_access_regions=matched,
        callsite_effects=matched_callsite_effects,
        function_effects=function_effects,
        module_declarations=module_declarations,
    )
    incomplete_loop_count = sum(
        1 for effect in loop_effects.values() if not effect["complete"]
    )
    indirect_call_targets = (
        parse_print_fp_targets(svf_output, module_calls)
        if collect_indirect_calls
        else {}
    )
    diagnostics = build_diagnostics(
        loop_effects=loop_effects,
        indirect_call_targets=indirect_call_targets,
        loop_diagnostics=loop_diagnostics,
        saber_diagnostics=saber_diagnostics,
        mta_diagnostics=mta_diagnostics,
    )

    oracle = {
        "schema_version": SCHEMA_VERSION,
        "producer": PRODUCER,
        "analysis": analysis,
        "memory_partition": memory_partition,
        "module_fingerprint": fnv1a64(module_keys),
        "access_regions": matched,
        "callsite_effects": matched_callsite_effects,
        "function_effects": function_effects,
        "loop_effects": loop_effects,
        "indirect_call_targets": indirect_call_targets,
        "diagnostics": diagnostics,
        "stats": {
            "module_access_count": len(module_keys),
            "module_call_count": len(module_calls),
            "svf_access_count": len(svf_access_regions),
            "svf_callsite_effect_count": len(parsed.callsite_effects),
            "matched_access_count": len(matched),
            "matched_callsite_effect_count": len(matched_callsite_effects),
            "unmatched_svf_access_count": len(svf_access_regions) - len(matched),
            "function_effect_count": len(function_effects),
            "incomplete_function_effect_count": incomplete_function_count,
            "loop_effect_count": len(loop_effects),
            "incomplete_loop_effect_count": incomplete_loop_count,
            "indirect_call_target_count": len(indirect_call_targets),
        },
    }
    return oracle


def run_svf(
    *,
    svf_wpa: Path,
    svf_extapi: Path,
    ll_path: Path,
    mem_par: str,
    timeout: int,
    collect_indirect_calls: bool = False,
) -> str:
    command = [
        str(svf_wpa),
        "-ander",
        "-svfg",
        "-dump-mssa",
        f"-mem-par={mem_par}",
        f"-extapi={svf_extapi}",
        str(ll_path),
    ]
    if collect_indirect_calls:
        command.insert(4, "-print-fp")
    try:
        completed = subprocess.run(
            command,
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
        raise AdapterError(
            f"SVF timed out after {timeout}s: {' '.join(command)}\n{output}"
        ) from exc

    if completed.returncode != 0:
        tail = "\n".join(completed.stdout.splitlines()[-40:])
        raise AdapterError(
            f"SVF failed with exit code {completed.returncode}: {' '.join(command)}\n{tail}"
        )
    return completed.stdout


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bc", required=True, type=Path, help="pre-BPL textual LLVM IR (.ll)")
    parser.add_argument("--out", required=True, type=Path, help="oracle JSON output path")
    parser.add_argument("--svf-wpa", default="wpa", type=Path, help="SVF wpa executable")
    parser.add_argument("--svf-extapi", default=None, type=Path, help="SVF extapi.bc path")
    parser.add_argument(
        "--mem-par",
        default="intra-disjoint",
        choices=("distinct", "intra-disjoint", "inter-disjoint"),
        help="SVF MemorySSA partition mode",
    )
    parser.add_argument("--timeout", default=300, type=int, help="SVF timeout in seconds")
    parser.add_argument(
        "--svf-output",
        default=None,
        type=Path,
        help="parse existing SVF dump instead of running wpa",
    )
    parser.add_argument(
        "--indirect-call-targets",
        action="store_true",
        default=False,
        help="parse SVF -print-fp indirect-call target output into the oracle",
    )
    parser.add_argument(
        "--loop-diagnostics",
        action="store_true",
        default=False,
        help="record loop-effect summary diagnostics",
    )
    parser.add_argument(
        "--saber-diagnostics",
        action="store_true",
        default=False,
        help="reserve SABER diagnostics in the oracle report",
    )
    parser.add_argument(
        "--mta-diagnostics",
        action="store_true",
        default=False,
        help="reserve MTA diagnostics in the oracle report",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    if args.bc.suffix != ".ll":
        raise AdapterError(
            "svf_memory_partition_adapter.py currently expects textual LLVM IR "
            "from `llvm2bpl -ll`, not bitcode"
        )

    ll_text = args.bc.read_text()
    sanitized_count = 0
    if args.svf_output is not None:
        svf_output = args.svf_output.read_text()
    else:
        if args.svf_extapi is None:
            raise AdapterError("--svf-extapi is required when running SVF")
        svf_input = args.bc
        sanitized_text, sanitized_count = sanitize_ir_for_svf(ll_text)
        temporary_svf_ir: tempfile.NamedTemporaryFile[str] | None = None
        if sanitized_count:
            temporary_svf_ir = tempfile.NamedTemporaryFile(
                mode="w",
                suffix=".svf.ll",
                prefix=f"{args.bc.stem}.",
                delete=False,
            )
            temporary_svf_ir.write(sanitized_text)
            temporary_svf_ir.close()
            svf_input = Path(temporary_svf_ir.name)
        svf_output = run_svf(
            svf_wpa=args.svf_wpa,
            svf_extapi=args.svf_extapi,
            ll_path=svf_input,
            mem_par=args.mem_par,
            timeout=args.timeout,
            collect_indirect_calls=args.indirect_call_targets,
        )

    oracle = build_oracle(
        ll_text=ll_text,
        svf_output=svf_output,
        analysis="andersen",
        memory_partition=args.mem_par,
        collect_indirect_calls=args.indirect_call_targets,
        loop_diagnostics=args.loop_diagnostics,
        saber_diagnostics=args.saber_diagnostics,
        mta_diagnostics=args.mta_diagnostics,
    )
    oracle["stats"]["svf_sanitized_gep_index_count"] = sanitized_count
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(oracle, indent=2, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except AdapterError as exc:
        print(f"error: {exc}", file=sys.stderr)
        raise SystemExit(1) from None

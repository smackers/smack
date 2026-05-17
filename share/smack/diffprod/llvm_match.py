from __future__ import annotations

import difflib
import re
from dataclasses import dataclass, field
from typing import Any


@dataclass
class LlvmInstruction:
    index: int
    text: str
    opcode: str
    exact: str
    shape: str


@dataclass
class LlvmBlock:
    function: str
    label: str
    instructions: list[LlvmInstruction] = field(default_factory=list)

    @property
    def exact_fingerprint(self) -> tuple[str, ...]:
        return tuple(inst.exact for inst in self.instructions)

    @property
    def shape_fingerprint(self) -> tuple[str, ...]:
        return tuple(inst.shape for inst in self.instructions)

    @property
    def opcodes(self) -> tuple[str, ...]:
        return tuple(inst.opcode for inst in self.instructions)


@dataclass
class LlvmFunction:
    name: str
    blocks: list[LlvmBlock] = field(default_factory=list)


@dataclass
class LlvmModule:
    functions: dict[str, LlvmFunction] = field(default_factory=dict)


_FUNC_RE = re.compile(r"^\s*define\b.*@(?P<name>[-.$A-Za-z_][-\w.$]*)\s*\(")
_BLOCK_RE = re.compile(r"^\s*(?P<label>[-.$A-Za-z_0-9]+):(?:\s|$)")
_ASSIGN_RE = re.compile(r"^\s*[%@][-.$A-Za-z_0-9]+\s*=\s*")
_SSA_VALUE_RE = re.compile(r"[%@][-.$A-Za-z_0-9]+")
_NUMBER_RE = re.compile(r"(?<![-.$A-Za-z_0-9])-?\d+(?![-.$A-Za-z_0-9])")
_METADATA_RE = re.compile(r",?\s*![A-Za-z_.]+ !\d+")
_ATTR_GROUP_RE = re.compile(r"\s+#\d+\b")


def build_llvm_match(
    *,
    left_ll: str,
    right_ll: str,
    left_entry: str,
    right_entry: str,
) -> dict[str, Any]:
    left = parse_llvm_ir(left_ll)
    right = parse_llvm_ir(right_ll)
    diagnostics: list[str] = []

    left_func = _select_function(left, left_entry, diagnostics, "left")
    right_func = _select_function(right, right_entry, diagnostics, "right")
    chunks: list[dict[str, Any]] = []
    if left_func is not None and right_func is not None:
        chunks = match_functions(left_func, right_func)

    stats = {
        "stable": sum(1 for c in chunks if c["kind"] == "stable"),
        "similar": sum(1 for c in chunks if c["kind"] == "similar"),
        "changed": sum(1 for c in chunks if c["kind"] == "changed"),
        "left_only": sum(1 for c in chunks if c["kind"] == "left_only"),
        "right_only": sum(1 for c in chunks if c["kind"] == "right_only"),
    }
    return {
        "version": 1,
        "left_entry": left_entry,
        "right_entry": right_entry,
        "chunks": chunks,
        "stats": stats,
        "diagnostics": diagnostics,
    }


def parse_llvm_ir(text: str) -> LlvmModule:
    module = LlvmModule()
    current_func: LlvmFunction | None = None
    current_block: LlvmBlock | None = None
    inst_index = 0

    for raw in text.splitlines():
        line = raw.strip()
        if not line or line.startswith(";"):
            continue
        if current_func is None:
            match = _FUNC_RE.match(line)
            if match:
                current_func = LlvmFunction(match.group("name"))
                module.functions[current_func.name] = current_func
                current_block = None
                inst_index = 0
            continue
        if line == "}":
            current_func = None
            current_block = None
            continue
        block_match = _BLOCK_RE.match(line)
        if block_match and not line.startswith("!"):
            current_block = LlvmBlock(current_func.name, block_match.group("label"))
            current_func.blocks.append(current_block)
            inst_index = 0
            continue
        if current_block is None:
            current_block = LlvmBlock(current_func.name, "entry")
            current_func.blocks.append(current_block)
            inst_index = 0
        if line.startswith(("!", "attributes ", "declare ")):
            continue
        opcode = _opcode(line)
        if not opcode:
            continue
        current_block.instructions.append(
            LlvmInstruction(
                index=inst_index,
                text=line,
                opcode=opcode,
                exact=_normalize_instruction(line, keep_constants=True),
                shape=_normalize_instruction(line, keep_constants=False),
            )
        )
        inst_index += 1

    return module


def match_functions(left: LlvmFunction, right: LlvmFunction) -> list[dict[str, Any]]:
    chunks: list[dict[str, Any]] = []
    used_right: set[int] = set()
    right_by_label = {block.label: index for index, block in enumerate(right.blocks)}

    for _left_index, left_block in enumerate(left.blocks):
        right_index = right_by_label.get(left_block.label)
        if right_index is None or right_index in used_right:
            right_index = _best_unmatched_block(left_block, right.blocks, used_right)

        if right_index is None:
            chunks.append(_chunk(f"m{len(chunks)}", "left_only", left_block, None, 0.0))
            continue

        right_block = right.blocks[right_index]
        used_right.add(right_index)
        similarity = _similarity(left_block, right_block)
        if left_block.exact_fingerprint == right_block.exact_fingerprint:
            kind = "stable"
        elif left_block.shape_fingerprint == right_block.shape_fingerprint or similarity >= 0.72:
            kind = "similar"
        else:
            kind = "changed"
        chunks.append(_chunk(f"m{len(chunks)}", kind, left_block, right_block, similarity))

    for right_index, right_block in enumerate(right.blocks):
        if right_index not in used_right:
            chunks.append(_chunk(f"m{len(chunks)}", "right_only", None, right_block, 0.0))

    return chunks


def _select_function(
    module: LlvmModule,
    entry: str,
    diagnostics: list[str],
    side: str,
) -> LlvmFunction | None:
    entry = entry.lstrip("@")
    if entry in module.functions:
        return module.functions[entry]
    escaped = entry.replace(".", "$")
    if escaped in module.functions:
        return module.functions[escaped]
    if len(module.functions) == 1:
        only = next(iter(module.functions.values()))
        diagnostics.append(f"{side}: entry {entry!r} not found; using only function {only.name!r}")
        return only
    diagnostics.append(
        f"{side}: entry {entry!r} not found in LLVM IR; available={sorted(module.functions)}"
    )
    return None


def _best_unmatched_block(
    left_block: LlvmBlock,
    right_blocks: list[LlvmBlock],
    used_right: set[int],
) -> int | None:
    best: tuple[float, int] | None = None
    for index, right_block in enumerate(right_blocks):
        if index in used_right:
            continue
        score = _similarity(left_block, right_block)
        if best is None or score > best[0]:
            best = (score, index)
    if best is None or best[0] < 0.50:
        return None
    return best[1]


def _similarity(left: LlvmBlock, right: LlvmBlock) -> float:
    left_items = list(left.shape_fingerprint or left.opcodes)
    right_items = list(right.shape_fingerprint or right.opcodes)
    if not left_items and not right_items:
        return 1.0
    return difflib.SequenceMatcher(a=left_items, b=right_items).ratio()


def _chunk(
    match_id: str,
    kind: str,
    left: LlvmBlock | None,
    right: LlvmBlock | None,
    similarity: float,
) -> dict[str, Any]:
    return {
        "match_id": match_id,
        "kind": kind,
        "similarity": round(float(similarity), 4),
        "left": _side_json(left),
        "right": _side_json(right),
    }


def _side_json(block: LlvmBlock | None) -> dict[str, Any] | None:
    if block is None:
        return None
    return {
        "function": block.function,
        "block": block.label,
        "instructions": [inst.index for inst in block.instructions],
        "opcodes": [inst.opcode for inst in block.instructions],
        "source_spans": [],
    }


def _opcode(line: str) -> str:
    text = _strip_instruction_noise(line)
    text = _ASSIGN_RE.sub("", text)
    if not text:
        return ""
    return text.split(None, 1)[0]


def _normalize_instruction(line: str, *, keep_constants: bool) -> str:
    text = _strip_instruction_noise(line)
    text = _ASSIGN_RE.sub("%result = ", text)
    text = _SSA_VALUE_RE.sub("%v", text)
    if not keep_constants:
        text = _NUMBER_RE.sub("#", text)
    return " ".join(text.split())


def _strip_instruction_noise(line: str) -> str:
    text = line.split(";", 1)[0].strip()
    text = _METADATA_RE.sub("", text)
    text = _ATTR_GROUP_RE.sub("", text)
    return text.rstrip(",")

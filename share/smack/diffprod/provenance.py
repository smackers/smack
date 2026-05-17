from __future__ import annotations

import ast as py_ast
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any


@dataclass(frozen=True)
class SourceSpan:
    file: str = ""
    start_line: int = 0
    end_line: int = 0
    start_col: int = 0
    end_col: int = 0

    def to_json(self) -> dict[str, Any]:
        return {
            "file": self.file,
            "start_line": self.start_line,
            "end_line": self.end_line,
            "start_col": self.start_col,
            "end_col": self.end_col,
        }


@dataclass
class OriginRecord:
    source_span: SourceSpan | None = None
    ast_id: str | None = None
    diff_hunk_id: str | None = None
    frontend_rule: str | None = None
    llvm_func: str | None = None
    llvm_bb: str | None = None
    llvm_inst_id: str | None = None
    llvm_op: str | None = None
    boogie_cmd_id: str | None = None
    synthetic_reason: str | None = None
    c_line: str | None = None
    cexpr: str | None = None
    attributes: dict[str, list[str]] = field(default_factory=dict)

    def to_json(self) -> dict[str, Any]:
        out: dict[str, Any] = {}
        if self.source_span is not None:
            out["source_span"] = self.source_span.to_json()
        for key in (
            "ast_id",
            "diff_hunk_id",
            "frontend_rule",
            "llvm_func",
            "llvm_bb",
            "llvm_inst_id",
            "llvm_op",
            "boogie_cmd_id",
            "synthetic_reason",
            "c_line",
            "cexpr",
        ):
            value = getattr(self, key)
            if value is not None:
                out[key] = value
        if self.attributes:
            out["attributes"] = self.attributes
        return out


@dataclass
class OriginSet:
    records: list[OriginRecord] = field(default_factory=list)

    def add(self, record: OriginRecord) -> None:
        self.records.append(record)

    def extend(self, other: OriginSet) -> None:
        self.records.extend(other.records)

    def primary_span(self) -> SourceSpan | None:
        for record in self.records:
            if record.source_span is not None and record.source_span.start_line:
                return record.source_span
        return None

    def source_spans(self) -> list[SourceSpan]:
        return [record.source_span for record in self.records if record.source_span is not None]

    def llvm_insts(self) -> set[str]:
        return {record.llvm_inst_id for record in self.records if record.llvm_inst_id is not None}

    def to_json(self) -> list[dict[str, Any]]:
        return [record.to_json() for record in self.records]


@dataclass
class ProvenanceIndex:
    origins: dict[str, OriginSet] = field(default_factory=dict)
    node_kinds: dict[str, str] = field(default_factory=dict)
    nodes: dict[str, Any] = field(default_factory=dict, repr=False)
    stmt_to_block: dict[str, str] = field(default_factory=dict)
    block_to_proc: dict[str, str] = field(default_factory=dict)
    block_labels: dict[str, str] = field(default_factory=dict)
    stmt_order: dict[str, list[str]] = field(default_factory=dict)
    proc_blocks: dict[str, list[str]] = field(default_factory=dict)

    def add_node(
        self,
        node_id: str,
        *,
        kind: str,
        node: Any,
        origins: OriginSet | None = None,
    ) -> None:
        self.node_kinds[node_id] = kind
        self.nodes[node_id] = node
        self.origins[node_id] = origins or OriginSet(
            [OriginRecord(ast_id=node_id, boogie_cmd_id=node_id)]
        )

    def origin_set(self, node_id: str) -> OriginSet:
        return self.origins.get(node_id, OriginSet())

    def source_statement_ids(self) -> list[str]:
        out: list[str] = []
        for node_id, kind in self.node_kinds.items():
            if kind != "stmt":
                continue
            span = self.origin_set(node_id).primary_span()
            if span is not None and span.start_line:
                out.append(node_id)
        return out

    def to_json(self, *, node_ids: set[str] | None = None) -> dict[str, Any]:
        ids = sorted(node_ids) if node_ids is not None else sorted(self.origins)
        return {
            node_id: {
                "kind": self.node_kinds.get(node_id),
                "origins": self.origin_set(node_id).to_json(),
            }
            for node_id in ids
            if node_id in self.origins
        }


@dataclass
class ParsedBoogieProgram:
    ast: Any
    declarations: list[Any]
    provenance: ProvenanceIndex
    source_name: str | None = None
    diagnostics: list[str] = field(default_factory=list)

    def procedures(self) -> list[Any]:
        ProcedureDeclaration = boogie_classes()["ProcedureDeclaration"]
        return [
            decl
            for decl in self.declarations
            if isinstance(decl, ProcedureDeclaration) and getattr(decl, "body", None)
        ]


def parse_boogie_with_provenance(
    text: str, *, source_name: str | None = None
) -> ParsedBoogieProgram:
    parser = boogie_parser()
    diagnostics: list[str] = []
    try:
        ast = parser.parse_boogie(text)
    except Exception:
        sanitized = normalize_smack_attributes(sanitize_smack_attribute_strings(text))
        if sanitized == text:
            raise
        ast = parser.parse_boogie(sanitized)
        diagnostics.append("normalized SMACK attribute syntax before parsing")
    declarations = normalise_declarations(ast)
    provenance = build_provenance_index(declarations)
    return ParsedBoogieProgram(
        ast=ast,
        declarations=declarations,
        provenance=provenance,
        source_name=source_name,
        diagnostics=diagnostics,
    )


def boogie_parser() -> Any:
    ensure_parent_repo_on_path()
    from interpreter.parser import boogie_parser as parser

    return parser


def boogie_classes() -> dict[str, Any]:
    ensure_parent_repo_on_path()
    from interpreter.parser.declaration import ProcedureDeclaration
    from interpreter.parser.expression import (
        ArithmeticNegation,
        BinaryExpression,
        BooleanLiteral,
        FunctionApplication,
        Identifier,
        IfExpression,
        IntegerLiteral,
        LogicalNegation,
        MapSelect,
        MapUpdate,
        StorageIdentifier,
    )
    from interpreter.parser.program import Program
    from interpreter.parser.statement import (
        AssertStatement,
        AssignStatement,
        AssumeStatement,
        CallStatement,
        GotoStatement,
        HavocStatement,
        IfStatement,
        ReturnStatement,
        WhileStatement,
    )

    return {
        "AssertStatement": AssertStatement,
        "AssignStatement": AssignStatement,
        "AssumeStatement": AssumeStatement,
        "ArithmeticNegation": ArithmeticNegation,
        "BinaryExpression": BinaryExpression,
        "BooleanLiteral": BooleanLiteral,
        "CallStatement": CallStatement,
        "FunctionApplication": FunctionApplication,
        "GotoStatement": GotoStatement,
        "HavocStatement": HavocStatement,
        "Identifier": Identifier,
        "IfExpression": IfExpression,
        "IfStatement": IfStatement,
        "IntegerLiteral": IntegerLiteral,
        "LogicalNegation": LogicalNegation,
        "MapSelect": MapSelect,
        "MapUpdate": MapUpdate,
        "ProcedureDeclaration": ProcedureDeclaration,
        "Program": Program,
        "ReturnStatement": ReturnStatement,
        "StorageIdentifier": StorageIdentifier,
        "WhileStatement": WhileStatement,
    }


def ensure_parent_repo_on_path() -> None:
    here = Path(__file__).resolve()
    for parent in here.parents:
        if (parent / "interpreter" / "parser" / "boogie_parser.py").exists():
            path = str(parent)
            if path not in sys.path:
                sys.path.insert(0, path)
            return


def normalise_declarations(ast_node: Any) -> list[Any]:
    Program = boogie_classes()["Program"]
    if isinstance(ast_node, Program):
        return list(ast_node.declarations)
    if isinstance(ast_node, list):
        return list(ast_node)
    return [ast_node]


def build_provenance_index(declarations: list[Any]) -> ProvenanceIndex:
    ProcedureDeclaration = boogie_classes()["ProcedureDeclaration"]
    index = ProvenanceIndex()
    for decl in declarations:
        if not isinstance(decl, ProcedureDeclaration) or getattr(decl, "body", None) is None:
            continue
        proc_id = proc_id_for(decl.name)
        index.add_node(
            proc_id,
            kind="proc",
            node=decl,
            origins=origins_for_node(proc_id, decl),
        )
        index.proc_blocks[proc_id] = []
        for block in decl.body.blocks:
            block_id = block_id_for(decl.name, block.name)
            index.add_node(
                block_id,
                kind="block",
                node=block,
                origins=origins_for_node(block_id, block),
            )
            index.block_to_proc[block_id] = proc_id
            index.block_labels[block_id] = block.name
            index.proc_blocks[proc_id].append(block_id)
            index.stmt_order[block_id] = []
            for stmt_index, stmt in enumerate(block.statements):
                stmt_id = stmt_id_for(decl.name, block.name, stmt_index)
                index.add_node(
                    stmt_id,
                    kind="stmt",
                    node=stmt,
                    origins=origins_for_node(stmt_id, stmt),
                )
                index.stmt_to_block[stmt_id] = block_id
                index.stmt_order[block_id].append(stmt_id)
                index.origin_set(block_id).extend(index.origin_set(stmt_id))
    return index


def origins_for_node(node_id: str, node: Any) -> OriginSet:
    origin = OriginSet([origin_record_for_node(node_id, node)])
    for child in structured_statement_children(node):
        origin.extend(origins_for_node(node_id, child))
    return origin


def origin_record_for_node(node_id: str, node: Any) -> OriginRecord:
    attrs = attribute_map(node)
    source_span = source_span_from_attrs(attrs)
    synthetic_reason = None
    if source_span is not None and is_synthetic_source(source_span):
        synthetic_reason = "synthetic_or_tool_source"
    verifier_code = attrs.get("verifier.code")
    record = OriginRecord(
        source_span=source_span,
        ast_id=node_id,
        frontend_rule=f"verifier.code:{verifier_code[0]}" if verifier_code else None,
        llvm_func=first(attrs.get("llvm.func")),
        llvm_bb=first(attrs.get("llvm.bb")),
        llvm_inst_id=first(attrs.get("llvm.inst")),
        llvm_op=first(attrs.get("llvm.op")),
        boogie_cmd_id=node_id,
        synthetic_reason=synthetic_reason,
        c_line=first(attrs.get("c_line")),
        cexpr=first(attrs.get("cexpr")),
        attributes=attrs,
    )
    return record


def structured_statement_children(node: Any) -> list[Any]:
    classes = boogie_classes()
    IfStatement = classes["IfStatement"]
    WhileStatement = classes["WhileStatement"]
    if not isinstance(node, (IfStatement, WhileStatement)):
        return []

    out: list[Any] = []
    for block in getattr(node, "blocks", []) or []:
        out.extend(getattr(block, "statements", []) or [])
    else_part = getattr(node, "else_", None)
    if isinstance(else_part, IfStatement):
        out.append(else_part)
    else:
        for block in else_part or []:
            out.extend(getattr(block, "statements", []) or [])
    return out


def attribute_map(node: Any) -> dict[str, list[str]]:
    out: dict[str, list[str]] = {}
    for attr in getattr(node, "attributes", []) or []:
        out[attr.key] = [attr_value_to_str(v) for v in getattr(attr, "values", [])]
    return out


def source_span_from_attrs(attrs: dict[str, list[str]]) -> SourceSpan | None:
    values = attrs.get("sourceloc")
    if not values or len(values) < 3:
        return None
    file_name = values[0]
    line = int_or_zero(values[1])
    col = int_or_zero(values[2])
    if not line:
        return SourceSpan(
            file=file_name,
            start_line=0,
            end_line=0,
            start_col=col,
            end_col=col,
        )
    return SourceSpan(
        file=file_name,
        start_line=line,
        end_line=line,
        start_col=col,
        end_col=col,
    )


def attr_value_to_str(value: Any) -> str:
    if isinstance(value, str):
        try:
            return str(py_ast.literal_eval(value))
        except (SyntaxError, ValueError):
            return value.strip('"')
    raw = getattr(value, "value", None)
    if raw is not None:
        return str(raw)
    name = getattr(value, "name", None)
    if name is not None:
        return str(name)
    return str(value)


def first(values: list[str] | None) -> str | None:
    return values[0] if values else None


def int_or_zero(value: str) -> int:
    try:
        return int(value)
    except ValueError:
        return 0


def is_synthetic_source(span: SourceSpan) -> bool:
    if span.start_line <= 0:
        return True
    normalized = span.file.replace("\\", "/")
    synthetic_parts = (
        "/smack/lib/",
        "/usr/local/share/smack/",
        "smack.c",
        "<unknown>",
    )
    return any(part in normalized for part in synthetic_parts)


def sanitize_smack_attribute_strings(text: str) -> str:
    for attr_name in ("c_line", "cexpr"):
        text = sanitize_string_attr(text, attr_name)
    return text


_SMACK_ATTRS_WITH_VALUES = {
    "sourceloc",
    "c_line",
    "cexpr",
    "llvm.func",
    "llvm.bb",
    "llvm.inst",
    "llvm.op",
    "diff.product",
    "diff.impacted",
    "diff.impacted.stmt",
    "diff.summary",
}


def normalize_smack_attributes(text: str) -> str:
    """Convert SMACK/Boogie space-separated attr values to parser syntax.

    Boogie attributes are normally written as `{:k v1 v2}`. The local parser
    accepts comma-separated values (`{:k v1, v2}`), so provenance parsing
    normalizes just the metadata attributes this pass consumes.
    """

    out: list[str] = []
    cursor = 0
    while True:
        start = text.find("{:", cursor)
        if start == -1:
            out.append(text[cursor:])
            break
        name_start = start + 2
        name_end = name_start
        while name_end < len(text) and not text[name_end].isspace() and text[name_end] != "}":
            name_end += 1
        name = text[name_start:name_end]
        close = find_attr_closing_brace(text, name_end)
        if close is None:
            out.append(text[cursor:])
            break
        if name not in _SMACK_ATTRS_WITH_VALUES:
            out.append(text[cursor : close + 1])
            cursor = close + 1
            continue
        payload = text[name_end:close].strip()
        out.append(text[cursor:name_end])
        if payload:
            out.append(" ")
            out.append(", ".join(split_attr_values(payload)))
        out.append("}")
        cursor = close + 1
    return "".join(out)


def find_attr_closing_brace(text: str, start: int) -> int | None:
    in_string = False
    escape = False
    i = start
    while i < len(text):
        ch = text[i]
        if in_string:
            if escape:
                escape = False
            elif ch == "\\":
                escape = True
            elif ch == '"':
                in_string = False
        elif ch == '"':
            in_string = True
        elif ch == "}":
            return i
        i += 1
    return None


def split_attr_values(payload: str) -> list[str]:
    values: list[str] = []
    cur: list[str] = []
    in_string = False
    escape = False
    for ch in payload:
        if in_string:
            cur.append(ch)
            if escape:
                escape = False
            elif ch == "\\":
                escape = True
            elif ch == '"':
                in_string = False
            continue
        if ch == '"':
            in_string = True
            cur.append(ch)
            continue
        if ch == "," or ch.isspace():
            if cur:
                values.append("".join(cur))
                cur = []
            continue
        cur.append(ch)
    if cur:
        values.append("".join(cur))
    return values


def sanitize_string_attr(text: str, attr_name: str) -> str:
    marker = f"{{:{attr_name} \""
    out: list[str] = []
    cursor = 0
    while True:
        start = text.find(marker, cursor)
        if start == -1:
            out.append(text[cursor:])
            break
        content_start = start + len(marker)
        closing_quote = find_attr_closing_quote(text, content_start)
        if closing_quote is None:
            out.append(text[cursor:])
            break
        out.append(text[cursor:content_start])
        out.append(escape_raw_quotes(text[content_start:closing_quote]))
        cursor = closing_quote
    return "".join(out)


def find_attr_closing_quote(text: str, start: int) -> int | None:
    i = start
    while i < len(text):
        if text[i] != '"':
            i += 1
            continue
        backslashes = 0
        j = i - 1
        while j >= start and text[j] == "\\":
            backslashes += 1
            j -= 1
        if backslashes % 2 == 1:
            i += 1
            continue
        k = i + 1
        while k < len(text) and text[k].isspace():
            k += 1
        if k < len(text) and text[k] == "}":
            return i
        i += 1
    return None


def escape_raw_quotes(value: str) -> str:
    out: list[str] = []
    for i, ch in enumerate(value):
        if ch == '"' and (i == 0 or value[i - 1] != "\\"):
            out.append('\\"')
        else:
            out.append(ch)
    return "".join(out)


def proc_id_for(proc_name: str) -> str:
    return f"proc:{proc_name}"


def block_id_for(proc_name: str, block_name: str) -> str:
    return f"proc:{proc_name}:block:{block_name}"


def stmt_id_for(proc_name: str, block_name: str, stmt_index: int) -> str:
    return f"proc:{proc_name}:block:{block_name}:stmt:{stmt_index}"

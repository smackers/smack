from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any

from .diff import DiffHunk, span_intersects_hunk
from .provenance import (
    ParsedBoogieProgram,
    ProvenanceIndex,
    boogie_classes,
    is_synthetic_source,
)


@dataclass
class ImpactReason:
    node_id: str
    reason: str
    via: str | None = None
    hunk_id: str | None = None
    variable: str | None = None

    def to_json(self) -> dict[str, Any]:
        out = {"node_id": self.node_id, "reason": self.reason}
        if self.via is not None:
            out["via"] = self.via
        if self.hunk_id is not None:
            out["hunk_id"] = self.hunk_id
        if self.variable is not None:
            out["variable"] = self.variable
        return out


@dataclass
class SideImpact:
    side: str
    impacted_blocks: set[str] = field(default_factory=set)
    impacted_statements: set[str] = field(default_factory=set)
    variables: set[str] = field(default_factory=set)
    reasons: dict[str, list[ImpactReason]] = field(default_factory=dict)

    def add_reason(self, reason: ImpactReason) -> None:
        self.reasons.setdefault(reason.node_id, []).append(reason)

    def to_json(self, provenance: ProvenanceIndex) -> dict[str, Any]:
        impacted_nodes = self.impacted_blocks | self.impacted_statements
        return {
            "side": self.side,
            "impacted_blocks": sorted(self.impacted_blocks),
            "impacted_statements": sorted(self.impacted_statements),
            "variables": sorted(self.variables),
            "reasons": {
                node_id: [r.to_json() for r in reasons]
                for node_id, reasons in sorted(self.reasons.items())
            },
            "provenance": provenance.to_json(node_ids=impacted_nodes),
        }


@dataclass
class ImpactResult:
    left: SideImpact
    right: SideImpact
    hunks: list[DiffHunk]
    diagnostics: list[str] = field(default_factory=list)

    def to_json(
        self,
        *,
        left_program: ParsedBoogieProgram | None = None,
        right_program: ParsedBoogieProgram | None = None,
    ) -> dict[str, Any]:
        left_prov = left_program.provenance if left_program is not None else ProvenanceIndex()
        right_prov = right_program.provenance if right_program is not None else ProvenanceIndex()
        return {
            "hunks": [hunk.to_json() for hunk in self.hunks],
            "left": self.left.to_json(left_prov),
            "right": self.right.to_json(right_prov),
            "diagnostics": self.diagnostics,
        }


def analyze_boogie_impact(
    left: ParsedBoogieProgram,
    right: ParsedBoogieProgram,
    hunks: list[DiffHunk],
) -> ImpactResult:
    diagnostics: list[str] = []
    return ImpactResult(
        left=analyze_side_impact(left, hunks, side="left", diagnostics=diagnostics),
        right=analyze_side_impact(right, hunks, side="right", diagnostics=diagnostics),
        hunks=hunks,
        diagnostics=diagnostics,
    )


def analyze_side_impact(
    parsed: ParsedBoogieProgram,
    hunks: list[DiffHunk],
    *,
    side: str,
    diagnostics: list[str],
) -> SideImpact:
    impact = SideImpact(side=side)
    prov = parsed.provenance
    source_stmt_ids = prov.source_statement_ids()
    if hunks and not source_stmt_ids:
        diagnostics.append(
            f"{side}: no source provenance found; conservatively impacting all blocks"
        )
        for block_id in prov.block_to_proc:
            mark_block(impact, prov, block_id, "missing-provenance")
        return impact

    for stmt_id in source_stmt_ids:
        origin = prov.origin_set(stmt_id)
        spans = [span for span in origin.source_spans() if not is_synthetic_source(span)]
        for hunk in hunks:
            if any(
                span_intersects_hunk(
                    source_file=span.file,
                    start_line=span.start_line,
                    end_line=span.end_line or span.start_line,
                    hunk=hunk,
                    side=side,
                )
                for span in spans
            ):
                block_id = prov.stmt_to_block[stmt_id]
                for seed_stmt_id in source_diff_seed_statements(parsed, stmt_id):
                    impact.impacted_statements.add(seed_stmt_id)
                    impact.add_reason(
                        ImpactReason(
                            node_id=seed_stmt_id,
                            reason="source-diff",
                            hunk_id=hunk.hunk_id,
                            via=None if seed_stmt_id == stmt_id else stmt_id,
                        )
                    )
                mark_block(impact, prov, block_id, "contains-diff-stmt", via=stmt_id)

    close_impact_fixpoint(parsed, impact)
    return impact


def close_impact_fixpoint(parsed: ParsedBoogieProgram, impact: SideImpact) -> None:
    """Close source/LLVM seeds through semantic dependencies.

    Textual diffs are only seeds. A changed value can affect a later unchanged
    branch, call argument, load address, or return; conversely, unrelated blocks
    between two independent diffs should not be pulled into the delta merely
    because they are between the hunks in CFG order. Iterate data and control
    closure to a fixpoint so newly impacted branch blocks can pull in their CFG
    successors, and newly pulled blocks can expose more data dependencies.
    """

    changed = True
    while changed:
        before = impact_snapshot(impact)
        close_data_deps(parsed, impact)
        close_cfg(parsed, impact)
        changed = impact_snapshot(impact) != before


def impact_snapshot(impact: SideImpact) -> tuple[frozenset[str], frozenset[str], frozenset[str]]:
    return (
        frozenset(impact.impacted_blocks),
        frozenset(impact.impacted_statements),
        frozenset(impact.variables),
    )


def source_diff_seed_statements(parsed: ParsedBoogieProgram, stmt_id: str) -> set[str]:
    """Include the semantic statement represented by a SMACK source marker.

    SMACK commonly emits a source-location `assume true` marker immediately
    before the real lowered Boogie command. The marker carries the C line but
    has no uses/defs, so dependency closure needs the following semantic
    statement as the actual seed.
    """

    prov = parsed.provenance
    stmt = prov.nodes.get(stmt_id)
    seeds = {stmt_id}
    if stmt is None or stmt_defs(stmt) or stmt_uses(stmt):
        return seeds

    block_id = prov.stmt_to_block.get(stmt_id)
    if block_id is None:
        return seeds
    stmt_order = prov.stmt_order.get(block_id, [])
    try:
        start = stmt_order.index(stmt_id) + 1
    except ValueError:
        return seeds

    for candidate_id in stmt_order[start:]:
        candidate = prov.nodes.get(candidate_id)
        if candidate is None:
            continue
        if is_semantic_seed_statement(candidate):
            seeds.add(candidate_id)
            break
        if prov.origin_set(candidate_id).primary_span() is not None:
            break
    return seeds


def is_semantic_seed_statement(stmt: Any) -> bool:
    classes = boogie_classes()
    return bool(stmt_defs(stmt) or stmt_uses(stmt)) or isinstance(
        stmt,
        (
            classes["CallStatement"],
            classes["HavocStatement"],
            classes["ReturnStatement"],
        ),
    )


def mark_block(
    impact: SideImpact,
    prov: ProvenanceIndex,
    block_id: str,
    reason: str,
    *,
    via: str | None = None,
) -> None:
    impact.impacted_blocks.add(block_id)
    impact.add_reason(ImpactReason(node_id=block_id, reason=reason, via=via))
    if reason == "contains-diff-stmt":
        return
    for stmt_id in prov.stmt_order.get(block_id, []):
        impact.impacted_statements.add(stmt_id)


def close_cfg(parsed: ParsedBoogieProgram, impact: SideImpact) -> None:
    prov = parsed.provenance
    for proc in parsed.procedures():
        cfg = cfg_for_proc(proc)
        proc_id = f"proc:{proc.name}"
        label_to_block_id = {
            prov.block_labels[block_id]: block_id for block_id in prov.proc_blocks.get(proc_id, [])
        }
        seed_labels = {
            prov.block_labels[block_id]
            for block_id in impact.impacted_blocks
            if prov.block_to_proc.get(block_id) == proc_id
        }
        if not seed_labels:
            continue

        labels_to_mark: dict[str, str] = {}
        for label in seed_labels:
            for pred, succs in cfg.items():
                if label in succs and len(succs) > 1:
                    labels_to_mark.setdefault(pred, "cfg-closure")
            if len(cfg.get(label, set())) > 1:
                for controlled in reachable_forward(cfg, {label}):
                    if controlled != label:
                        labels_to_mark[controlled] = "control-dependency"

        for label, reason in labels_to_mark.items():
            block_id = label_to_block_id.get(label)
            if block_id is not None:
                if block_id not in impact.impacted_blocks:
                    mark_block(impact, prov, block_id, reason)
                else:
                    impact.add_reason(ImpactReason(node_id=block_id, reason=reason))


def cfg_for_proc(proc: Any) -> dict[str, set[str]]:
    GotoStatement = boogie_classes()["GotoStatement"]
    cfg: dict[str, set[str]] = {block.name: set() for block in proc.body.blocks}
    for block in proc.body.blocks:
        if not block.statements:
            continue
        last_stmt = block.statements[-1]
        if isinstance(last_stmt, GotoStatement):
            cfg[block.name].update(ident.name for ident in last_stmt.identifiers)
    return cfg


def reachable_forward(cfg: dict[str, set[str]], seeds: set[str]) -> set[str]:
    seen = set(seeds)
    work = list(seeds)
    while work:
        cur = work.pop()
        for succ in cfg.get(cur, set()):
            if succ not in seen:
                seen.add(succ)
                work.append(succ)
    return seen


def close_data_deps(parsed: ParsedBoogieProgram, impact: SideImpact) -> None:
    prov = parsed.provenance
    variables_by_proc: dict[str, set[str]] = {}

    changed = True
    while changed:
        changed = False
        before_vars = {
            proc_id: frozenset(variables) for proc_id, variables in variables_by_proc.items()
        }
        for stmt_id in list(impact.impacted_statements):
            stmt = prov.nodes.get(stmt_id)
            block_id = prov.stmt_to_block.get(stmt_id)
            proc_id = prov.block_to_proc.get(block_id or "")
            if stmt is not None and proc_id is not None:
                variables = variables_by_proc.setdefault(proc_id, set())
                variables.update(stmt_defs(stmt))
                variables.update(stmt_uses(stmt))
        after_vars = {
            proc_id: frozenset(variables) for proc_id, variables in variables_by_proc.items()
        }
        changed = changed or after_vars != before_vars

        for stmt_id, kind in prov.node_kinds.items():
            if kind != "stmt" or stmt_id in impact.impacted_statements:
                continue
            stmt = prov.nodes[stmt_id]
            defs = stmt_defs(stmt)
            uses = stmt_uses(stmt)
            block_id = prov.stmt_to_block[stmt_id]
            proc_id = prov.block_to_proc.get(block_id)
            variables = variables_by_proc.setdefault(proc_id or "", set())
            overlap = variables & (defs | uses)
            if not overlap:
                continue
            impact.impacted_statements.add(stmt_id)
            mark_block(impact, prov, block_id, "data-dependency", via=stmt_id)
            for var in sorted(overlap):
                impact.add_reason(
                    ImpactReason(
                        node_id=stmt_id,
                        reason="data-dependency",
                        variable=var,
                    )
                )
            before = set(variables)
            variables.update(defs)
            variables.update(uses)
            changed = changed or variables != before
    for variables in variables_by_proc.values():
        impact.variables.update(variables)


def stmt_defs(stmt: Any) -> set[str]:
    classes = boogie_classes()
    if isinstance(stmt, classes["AssignStatement"]):
        return {name for lhs in stmt.lhs if (name := lhs_root_name(lhs))}
    if isinstance(stmt, classes["HavocStatement"]):
        return {ident.name for ident in stmt.identifiers}
    if isinstance(stmt, classes["CallStatement"]):
        return {ident.name for ident in stmt.assignments}
    return set()


def stmt_uses(stmt: Any) -> set[str]:
    classes = boogie_classes()
    if isinstance(stmt, classes["AssignStatement"]):
        out: set[str] = set()
        for rhs in stmt.rhs:
            out.update(expr_vars(rhs))
        for lhs in stmt.lhs:
            out.update(lhs_uses(lhs))
        return out
    if isinstance(stmt, (classes["AssertStatement"], classes["AssumeStatement"])):
        return expr_vars(stmt.expression)
    if isinstance(stmt, classes["CallStatement"]):
        out: set[str] = set()
        for arg in stmt.arguments:
            out.update(expr_vars(arg))
        return out
    if isinstance(stmt, classes["ReturnStatement"]):
        expr = getattr(stmt, "expression", None)
        return expr_vars(expr) if expr is not None else set()
    return set()


def expr_vars(expr: Any) -> set[str]:
    if expr is None:
        return set()
    Identifier = boogie_classes()["Identifier"]
    if isinstance(expr, Identifier):
        return {expr.name}
    out: set[str] = set()
    if hasattr(expr, "each"):
        for node in expr.each():
            if node is expr:
                continue
            if isinstance(node, Identifier):
                out.add(node.name)
    return out


def lhs_root_name(lhs: Any) -> str | None:
    classes = boogie_classes()
    cur = lhs
    while isinstance(cur, classes["MapSelect"]):
        cur = cur.map
    return cur.name if isinstance(cur, classes["Identifier"]) else None


def lhs_uses(lhs: Any) -> set[str]:
    MapSelect = boogie_classes()["MapSelect"]
    if not isinstance(lhs, MapSelect):
        return set()
    root = lhs_root_name(lhs)
    uses = {root} if root else set()
    cur = lhs
    while isinstance(cur, MapSelect):
        for idx in cur.indexes:
            uses.update(expr_vars(idx))
        cur = cur.map
    return uses

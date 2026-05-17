from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any

from .impact import ImpactResult
from .provenance import ParsedBoogieProgram, ProvenanceIndex


@dataclass(frozen=True)
class SummaryRegion:
    side: str
    block_id: str
    block_label: str
    proc_id: str | None
    equivalent_to: str | None = None
    signature: str = ""

    def to_json(self) -> dict[str, Any]:
        out = {
            "side": self.side,
            "block_id": self.block_id,
            "block_label": self.block_label,
            "proc_id": self.proc_id,
            "signature": self.signature,
        }
        if self.equivalent_to is not None:
            out["equivalent_to"] = self.equivalent_to
        return out


@dataclass
class SummaryPlan:
    left: list[SummaryRegion] = field(default_factory=list)
    right: list[SummaryRegion] = field(default_factory=list)
    diagnostics: list[str] = field(default_factory=list)

    def to_json(self) -> dict[str, Any]:
        return {
            "left": [region.to_json() for region in self.left],
            "right": [region.to_json() for region in self.right],
            "diagnostics": self.diagnostics,
        }


def build_summary_plan(
    left: ParsedBoogieProgram,
    right: ParsedBoogieProgram,
    impact: ImpactResult,
) -> SummaryPlan:
    """Summarize blocks outside the impact cut and pair equivalent regions."""

    left_sigs = block_signatures(left.provenance)
    right_sigs = block_signatures(right.provenance)
    right_by_sig: dict[str, list[str]] = {}
    for block_id, signature in right_sigs.items():
        if block_id in impact.right.impacted_blocks:
            continue
        right_by_sig.setdefault(signature, []).append(block_id)

    plan = SummaryPlan()
    used_right: set[str] = set()
    for block_id, signature in sorted(left_sigs.items()):
        if block_id in impact.left.impacted_blocks:
            continue
        match = next(
            (
                candidate
                for candidate in right_by_sig.get(signature, [])
                if candidate not in used_right
            ),
            None,
        )
        if match is not None:
            used_right.add(match)
        plan.left.append(
            make_region(
                "left",
                left.provenance,
                block_id,
                signature=signature,
                equivalent_to=match,
            )
        )

    left_by_sig: dict[str, list[str]] = {}
    for block_id, signature in left_sigs.items():
        if block_id in impact.left.impacted_blocks:
            continue
        left_by_sig.setdefault(signature, []).append(block_id)

    used_left = {region.equivalent_to for region in plan.left if region.equivalent_to is not None}
    for block_id, signature in sorted(right_sigs.items()):
        if block_id in impact.right.impacted_blocks:
            continue
        match = next(
            (
                candidate
                for candidate in left_by_sig.get(signature, [])
                if candidate not in used_left
            ),
            None,
        )
        plan.right.append(
            make_region(
                "right",
                right.provenance,
                block_id,
                signature=signature,
                equivalent_to=match,
            )
        )

    if not plan.left and not plan.right:
        plan.diagnostics.append("no unchanged Boogie blocks available for summaries")
    return plan


def block_signatures(provenance: ProvenanceIndex) -> dict[str, str]:
    out: dict[str, str] = {}
    for block_id, stmt_ids in provenance.stmt_order.items():
        parts: list[str] = []
        for stmt_id in stmt_ids:
            node = provenance.nodes.get(stmt_id)
            origin = provenance.origin_set(stmt_id)
            op = next(
                (record.llvm_op for record in origin.records if record.llvm_op is not None),
                None,
            )
            cexpr = next(
                (record.cexpr for record in origin.records if record.cexpr is not None),
                None,
            )
            parts.append(f"{type(node).__name__}:{op or ''}:{cexpr or ''}")
        out[block_id] = "|".join(parts)
    return out


def make_region(
    side: str,
    provenance: ProvenanceIndex,
    block_id: str,
    *,
    signature: str,
    equivalent_to: str | None,
) -> SummaryRegion:
    return SummaryRegion(
        side=side,
        block_id=block_id,
        block_label=provenance.block_labels.get(block_id, block_id),
        proc_id=provenance.block_to_proc.get(block_id),
        equivalent_to=equivalent_to,
        signature=signature,
    )

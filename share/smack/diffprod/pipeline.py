from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any

from .diff import parse_unified_diff
from .failure_cut import CutEntry, failure_cut_from_text, provisional_failure_cut
from .impact import ImpactReason, ImpactResult, analyze_boogie_impact, mark_block
from .product import ProductArtifact, build_product_artifact
from .provenance import ParsedBoogieProgram, parse_boogie_with_provenance
from .summaries import SummaryPlan, build_summary_plan


@dataclass
class EquivalenceCheck:
    checked: bool = False
    verified: bool | None = None
    result: str | None = None
    return_code: int | None = None
    output_tail: str = ""

    def to_json(self) -> dict[str, Any]:
        return {
            "checked": self.checked,
            "verified": self.verified,
            "result": self.result,
            "return_code": self.return_code,
            "output_tail": self.output_tail,
        }


@dataclass
class DiffProductResult:
    left: ParsedBoogieProgram
    right: ParsedBoogieProgram
    impact: ImpactResult
    summaries: SummaryPlan
    product: ProductArtifact
    llvm_match: dict[str, Any] | None = None
    failure_cut: list[CutEntry] = field(default_factory=list)
    diagnostics: list[str] = field(default_factory=list)
    equivalence: EquivalenceCheck = field(default_factory=EquivalenceCheck)

    def to_json(self) -> dict[str, Any]:
        return {
            "impact": self.impact.to_json(
                left_program=self.left,
                right_program=self.right,
            ),
            "summaries": self.summaries.to_json(),
            "product": self.product.to_json(),
            "llvm_match": self.llvm_match,
            "equivalence": self.equivalence.to_json(),
            "failure_cut": [entry.to_json() for entry in self.failure_cut],
            "diagnostics": self.diagnostics,
        }


def build_from_bpl(
    *,
    left_bpl: str,
    right_bpl: str,
    diff_text: str,
    left_name: str = "left",
    right_name: str = "right",
    left_entry: str | None = None,
    right_entry: str | None = None,
    verifier_output: str | None = None,
    alignment: str = "auto",
    no_egraph: bool = False,
    egraph_timeout_s: int = 10,
    llvm_match: dict[str, Any] | None = None,
) -> DiffProductResult:
    hunks = parse_unified_diff(diff_text)
    left = parse_boogie_with_provenance(left_bpl, source_name=left_name)
    right = parse_boogie_with_provenance(right_bpl, source_name=right_name)
    impact = analyze_boogie_impact(left, right, hunks)
    if llvm_match is not None:
        apply_llvm_match_impact(left, right, impact, llvm_match)
    summaries = build_summary_plan(left, right, impact)
    product = build_product_artifact(
        left_text=left_bpl,
        right_text=right_bpl,
        diff_text=diff_text,
        left=left,
        right=right,
        impact=impact,
        summaries=summaries,
        left_entry=left_entry,
        right_entry=right_entry,
        alignment=alignment,
        no_egraph=no_egraph,
        egraph_timeout_s=egraph_timeout_s,
        llvm_match=llvm_match,
    )
    if verifier_output:
        failure_cut = failure_cut_from_text(left, right, verifier_output)
    else:
        failure_cut = provisional_failure_cut(left, right, impact)
    diagnostics: list[str] = []
    diagnostics.extend(left.diagnostics)
    diagnostics.extend(right.diagnostics)
    diagnostics.extend(impact.diagnostics)
    diagnostics.extend(summaries.diagnostics)
    diagnostics.extend(product.diagnostics)
    return DiffProductResult(
        left=left,
        right=right,
        impact=impact,
        summaries=summaries,
        product=product,
        llvm_match=llvm_match,
        failure_cut=failure_cut,
        diagnostics=diagnostics,
    )


def apply_llvm_match_impact(
    left: ParsedBoogieProgram,
    right: ParsedBoogieProgram,
    impact: ImpactResult,
    llvm_match: dict[str, Any],
) -> None:
    """Seed impact from LLVM matcher chunks.

    Stable chunks are intentionally ignored. Every other chunk is a product
    region candidate, so we mark the corresponding Boogie block when SMACK
    provenance can connect `llvm.func`/`llvm.bb` back to the emitted BPL.
    """

    for chunk in llvm_match.get("chunks", []) or []:
        kind = chunk.get("kind")
        if kind == "stable":
            continue
        match_id = chunk.get("match_id")
        for side_name, parsed, side_impact in (
            ("left", left, impact.left),
            ("right", right, impact.right),
        ):
            side = chunk.get(side_name)
            if not side:
                continue
            for block_id in blocks_for_llvm_side(parsed, side):
                mark_block(
                    side_impact,
                    parsed.provenance,
                    block_id,
                    f"llvm-match-{kind}",
                )
                side_impact.add_reason(
                    ImpactReason(
                        node_id=block_id,
                        reason="llvm-match",
                        via=match_id,
                    )
                )


def blocks_for_llvm_side(
    parsed: ParsedBoogieProgram,
    side: dict[str, Any],
) -> set[str]:
    func = str(side.get("function") or "")
    block = str(side.get("block") or "")
    instructions = {f"{func}:{block}:{index}" for index in side.get("instructions", []) or []}
    out: set[str] = set()
    for block_id in parsed.provenance.block_to_proc:
        origins = parsed.provenance.origin_set(block_id)
        for record in origins.records:
            if record.llvm_inst_id in instructions:
                out.add(block_id)
                break
            if record.llvm_func == func and record.llvm_bb == block:
                out.add(block_id)
                break
    return out

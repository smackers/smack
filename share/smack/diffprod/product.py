from __future__ import annotations

import os
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from .impact import ImpactResult
from .provenance import ParsedBoogieProgram
from .summaries import SummaryPlan


@dataclass
class ProductArtifact:
    text: str
    actual_product_available: bool
    diagnostics: list[str] = field(default_factory=list)
    mode: str | None = None
    actual_source: str | None = None
    delta_left_blocks: list[str] = field(default_factory=list)
    delta_right_blocks: list[str] = field(default_factory=list)
    lockstep_outcomes: list[dict[str, Any]] = field(default_factory=list)
    egraph_outcomes: list[dict[str, Any]] = field(default_factory=list)
    structural: dict[str, Any] | None = None
    selection: list[dict[str, Any]] = field(default_factory=list)

    def to_json(self) -> dict[str, Any]:
        return {
            "actual_product_available": self.actual_product_available,
            "actual_source": self.actual_source,
            "mode": self.mode,
            "structural": self.structural,
            "selection": self.selection,
            "delta": {
                "left_blocks": self.delta_left_blocks,
                "right_blocks": self.delta_right_blocks,
            },
            "lockstep_outcomes": self.lockstep_outcomes,
            "egraph_outcomes": self.egraph_outcomes,
            "egraph_success": any(
                outcome.get("success") and is_egraph_resolution(outcome.get("resolution"))
                for outcome in self.egraph_outcomes
            ),
            "diagnostics": self.diagnostics,
        }


def is_egraph_resolution(resolution: Any) -> bool:
    return str(resolution or "").startswith("egraph")


def _blocks_from_stmt_ids(stmt_ids: set[str]) -> set[str]:
    """Project stmt-ids ("proc:N:block:L:stmt:I") to bare block labels ("L").

    deltarel's ``StmtClassification.delta`` is keyed by stmt-id; SMACK's
    ``delta_left_blocks`` / ``delta_right_blocks`` fields surface bare block
    names for the regtest contract (`report["product"]["delta"]["left_blocks"]
    == ["hot"]`). This helper bridges the contract mismatch.
    """
    blocks: set[str] = set()
    for sid in stmt_ids:
        parts = sid.split(":")
        try:
            i = parts.index("block")
            blocks.add(parts[i + 1])
        except (ValueError, IndexError):
            pass
    return blocks


def build_product_artifact(
    *,
    left_text: str,
    right_text: str,
    diff_text: str,
    left: ParsedBoogieProgram,
    right: ParsedBoogieProgram,
    impact: ImpactResult,
    summaries: SummaryPlan,
    left_entry: str | None = None,
    right_entry: str | None = None,
    alignment: str = "auto",
    no_egraph: bool = False,
    egraph_timeout_s: int = 10,
    llvm_match: dict[str, Any] | None = None,
) -> ProductArtifact:
    """Build the product output for this slice.

    The existing product pass is used when it can lower the selected Boogie
    procedures. SMACK-generated Boogie often contains memory-model constructs
    outside that subset, so this function always falls back to a valid Boogie
    impact/summary artifact instead of failing the whole pipeline.
    """

    diagnostics: list[str] = []
    actual = try_build_generic_product(
        left_text=left_text,
        right_text=right_text,
        diff_text=diff_text,
        left=left,
        right=right,
        impact=impact,
        left_entry=left_entry,
        right_entry=right_entry,
        alignment=alignment,
        no_egraph=no_egraph,
        egraph_timeout_s=egraph_timeout_s,
        llvm_match=llvm_match,
        diagnostics=diagnostics,
    )
    if actual is not None:
        return actual

    diagnostics.append(
        "emitted impact/summary product artifact because selected SMACK Boogie "
        "was outside the current relational-product lowering subset"
    )
    return ProductArtifact(
        text=emit_metadata_product(left, right, impact, summaries),
        actual_product_available=False,
        diagnostics=diagnostics,
        delta_left_blocks=sorted(_blocks_from_stmt_ids(impact.left.impacted_blocks)),
        delta_right_blocks=sorted(_blocks_from_stmt_ids(impact.right.impacted_blocks)),
    )


def try_build_actual_product(
    *,
    left_text: str,
    right_text: str,
    diff_text: str,
    left_entry: str | None,
    right_entry: str | None,
    diagnostics: list[str],
) -> str | None:
    artifact = try_build_generic_product(
        left_text=left_text,
        right_text=right_text,
        diff_text=diff_text,
        left_entry=left_entry,
        right_entry=right_entry,
        alignment="auto",
        no_egraph=False,
        egraph_timeout_s=10,
        diagnostics=diagnostics,
    )
    return artifact.text if artifact is not None else None


def try_build_generic_product(
    *,
    left_text: str,
    right_text: str,
    diff_text: str,
    left: ParsedBoogieProgram | None = None,
    right: ParsedBoogieProgram | None = None,
    impact: ImpactResult | None = None,
    left_entry: str | None,
    right_entry: str | None,
    alignment: str,
    no_egraph: bool,
    egraph_timeout_s: int,
    llvm_match: dict[str, Any] | None = None,
    diagnostics: list[str],
) -> ProductArtifact | None:
    if not ensure_diffprod_package_on_path():
        diagnostics.append("diffprod library product pass was not found")
        return None
    try:
        from diffprod.product_v2 import build_product_ast
    except Exception as exc:
        diagnostics.append(f"failed to import diffprod product_v2 pass: {exc}")
        return None

    proc_name: str | None
    if left_entry or right_entry:
        if right_entry is not None and left_entry is not None and right_entry != left_entry:
            diagnostics.append(
                "actual product construction currently requires matching left/right entries"
            )
            return None
        proc_name = left_entry or right_entry
    else:
        proc_name = None
    if proc_name is None:
        diagnostics.append("actual product construction requires an entry procedure")
        return None
    if left is None or right is None or impact is None:
        diagnostics.append("actual product construction requires parsed impact data")
        return None

    try:
        llvm_left_blocks = impacted_blocks_from_llvm_match(left, "left", llvm_match)
        llvm_right_blocks = impacted_blocks_from_llvm_match(right, "right", llvm_match)
        left_block_markers = product_block_marker_ids(impact.left) | llvm_left_blocks
        right_block_markers = product_block_marker_ids(impact.right) | llvm_right_blocks
        tagged_left = mark_impacted_statements(
            left,
            impact.left.impacted_statements,
            left_block_markers,
        )
        tagged_right = mark_impacted_statements(
            right,
            impact.right.impacted_statements,
            right_block_markers,
        )
        result = build_product_ast(
            tagged_left,
            tagged_right,
            proc_name,
            diff_text=diff_text,
            disable_egraph=no_egraph or alignment == "baseline",
            egraph_timeout_s=egraph_timeout_s,
        )
    except Exception as exc:
        diagnostics.append(f"actual product construction failed: {exc}")
        return None

    diagnostics.extend(getattr(result, "diagnostics", []) or [])
    text = strip_smack_instrumentation(result.program_text)
    text = prepend_support_declarations(text, left_text, right_text)
    # Union deltarel's classifier output with SMACK's own impacted-block set.
    # deltarel's `classification_*.delta` is empty for SMACK's `:diff_affected`
    # seeding pattern (upstream algorithm gap). Falling back to SMACK's
    # `impact.{left,right}.impacted_blocks` keeps the regtest contract
    # (`report["product"]["delta"]["left_blocks"]`) accurate without waiting
    # on a deltarel-side change.
    delta_left = _blocks_from_stmt_ids(result.classification_p.delta) | _blocks_from_stmt_ids(
        impact.left.impacted_blocks
    )
    delta_right = _blocks_from_stmt_ids(result.classification_q.delta) | _blocks_from_stmt_ids(
        impact.right.impacted_blocks
    )
    return ProductArtifact(
        text=add_trace_pair_comments(text, result),
        actual_product_available=True,
        diagnostics=list(diagnostics),
        mode=alignment if alignment != "auto" else "functional-equivalence",
        actual_source="diffprod-product-v2",
        delta_left_blocks=sorted(delta_left),
        delta_right_blocks=sorted(delta_right),
        lockstep_outcomes=[],
        egraph_outcomes=[egraph_outcome_json(o) for o in result.align_outcomes],
        structural=None,
        selection=[
            {
                "selected": True,
                "mode": alignment if alignment != "auto" else "functional-equivalence",
                "source": "diffprod-product-v2",
                "stable_pair_count": result.stable_pair_count,
                "delta_region_count": result.delta_region_count,
            }
        ],
    )


def product_block_marker_ids(side_impact: Any) -> set[str]:
    """Blocks that should receive one block-level diff marker.

    A block that merely contains a source-diff statement is not enough:
    statement-level markers already carry that seed. Marking the first
    statement of such a block destroys diff precision when structured
    lowering emits a whole function or loop nest in one Boogie block.
    """
    out: set[str] = set()
    for block_id in side_impact.impacted_blocks:
        reasons = {
            getattr(reason, "reason", "") for reason in side_impact.reasons.get(block_id, []) or []
        }
        if reasons and reasons <= {"contains-diff-stmt"}:
            continue
        out.add(block_id)
    return out


def prepend_support_declarations(product_text: str, *source_texts: str) -> str:
    """Preserve SMACK type/function prelude needed by the emitted product."""
    decls: list[str] = []
    seen: set[str] = set()
    prefixes = ("type ", "const ", "function ", "axiom ")
    for source in source_texts:
        for line in source.splitlines():
            stripped = line.strip()
            if not stripped or stripped in seen:
                continue
            if stripped.startswith(prefixes):
                seen.add(stripped)
                decls.append(stripped)
                continue
            if stripped.startswith("var "):
                for side_decl in suffixed_global_var_decls(stripped):
                    if side_decl not in seen:
                        seen.add(side_decl)
                        decls.append(side_decl)
    if not decls:
        return product_text
    return "\n".join(decls) + "\n\n" + product_text


def suffixed_global_var_decls(line: str) -> list[str]:
    if not line.endswith(";") or ":" not in line:
        return []
    body = line[len("var ") : -1]
    names_part, type_part = body.split(":", 1)
    names = [name.strip() for name in names_part.split(",") if name.strip()]
    out: list[str] = []
    for name in names:
        if name != "$exn":
            continue
        if name.endswith(".P") or name.endswith(".Q"):
            continue
        out.append(f"var {name}.P:{type_part};")
        out.append(f"var {name}.Q:{type_part};")
    return out


def strip_smack_instrumentation(product_text: str) -> str:
    """Drop source/provenance recording calls that are not part of the product."""
    out: list[str] = []
    for line in product_text.splitlines():
        stripped = line.strip()
        if stripped.startswith("call $initialize("):
            continue
        if "boogie_si_record_" in stripped:
            continue
        if stripped.startswith("$exn.") and ":=" in stripped:
            continue
        out.append(line)
    return "\n".join(out) + ("\n" if product_text.endswith("\n") else "")


def mark_impacted_statements(
    parsed: ParsedBoogieProgram,
    impacted_statement_ids: set[str],
    impacted_block_ids: set[str],
) -> str:
    """Return Boogie text with ``:diff_affected`` markers before impacted stmts."""
    if not impacted_statement_ids and not impacted_block_ids:
        return str(parsed.ast)

    from diffprod.boogie_bridge import _boogie_classes
    from interpreter.parser.node import Attribute

    classes = _boogie_classes()
    AssumeStatement = classes["AssumeStatement"]
    AssignStatement = classes["AssignStatement"]
    BooleanLiteral = classes["BooleanLiteral"]
    CallStatement = classes["CallStatement"]
    HavocStatement = classes["HavocStatement"]
    IfStatement = classes["IfStatement"]
    ProcedureDeclaration = classes["ProcedureDeclaration"]
    WhileStatement = classes["WhileStatement"]

    def marker() -> Any:
        return AssumeStatement(
            attributes=[
                Attribute(
                    key="diff_affected",
                    values=[BooleanLiteral(value=True)],
                )
            ],
            expression=BooleanLiteral(value=True),
        )

    program = parsed.ast.clone()
    for decl in getattr(program, "declarations", []) or []:
        if not isinstance(decl, ProcedureDeclaration) or getattr(decl, "body", None) is None:
            continue
        for block in decl.body.blocks:
            block_id = f"proc:{decl.name}:block:{block.name}"
            block_mark_index = None
            if block_id in impacted_block_ids:
                preferred = (WhileStatement, IfStatement, AssignStatement)
                fallback = (CallStatement, HavocStatement)
                for index, candidate in enumerate(block.statements):
                    if isinstance(candidate, preferred):
                        block_mark_index = index
                        break
                if block_mark_index is None:
                    for index, candidate in enumerate(block.statements):
                        if isinstance(candidate, fallback):
                            block_mark_index = index
                            break
            new_stmts: list[Any] = []
            for stmt_index, stmt in enumerate(block.statements):
                stmt_id = f"proc:{decl.name}:block:{block.name}:stmt:{stmt_index}"
                if stmt_id in impacted_statement_ids or stmt_index == block_mark_index:
                    new_stmts.append(marker())
                new_stmts.append(stmt)
            block.statements = new_stmts
    return str(program)


def impacted_blocks_from_llvm_match(
    parsed: ParsedBoogieProgram,
    side_name: str,
    llvm_match: dict[str, Any] | None,
) -> set[str]:
    if not llvm_match:
        return set()
    wanted: set[tuple[str, str]] = set()
    for chunk in llvm_match.get("chunks", []) or []:
        if chunk.get("kind") == "stable":
            continue
        side = chunk.get(side_name) or {}
        func = str(side.get("function") or "")
        block = str(side.get("block") or "")
        if func and block:
            wanted.add((func, block))
    if not wanted:
        return set()

    from diffprod.boogie_bridge import _boogie_classes

    classes = _boogie_classes()
    ProcedureDeclaration = classes["ProcedureDeclaration"]
    out: set[str] = set()
    for decl in parsed.declarations:
        if not isinstance(decl, ProcedureDeclaration) or getattr(decl, "body", None) is None:
            continue
        for boogie_block in decl.body.blocks:
            text = str(boogie_block)
            for func, llvm_block in wanted:
                if (f'{{:llvm.func "{func}"}}') in text and (
                    f'{{:llvm.bb "{llvm_block}"}}'
                ) in text:
                    out.add(f"proc:{decl.name}:block:{boogie_block.name}")
                    break
    return out


def product_artifact_from_result(
    *,
    text: str,
    result: Any,
    diagnostics: list[str],
    actual_source: str,
) -> ProductArtifact:
    return ProductArtifact(
        text=add_trace_pair_comments(text, result),
        actual_product_available=True,
        diagnostics=list(diagnostics),
        mode=result.mode,
        actual_source=actual_source,
        delta_left_blocks=sorted(result.delta.delta_p),
        delta_right_blocks=sorted(result.delta.delta_q),
        lockstep_outcomes=[lockstep_outcome_json(o) for o in result.lockstep_outcomes],
        egraph_outcomes=[egraph_outcome_json(o) for o in result.align_outcomes],
        structural=structural_json(getattr(result, "structural", None)),
        selection=[
            candidate.to_json() for candidate in getattr(result, "candidate_reports", []) or []
        ],
    )


def structural_json(value: Any) -> dict[str, Any] | None:
    if value is None:
        return None
    return {
        "block_count": value.block_count,
        "stmt_count": value.stmt_count,
        "p_block_count": value.p_block_count,
        "q_block_count": value.q_block_count,
        "cartesian_pair_cost": value.cartesian_pair_cost,
        "cross_side_assert_count": value.cross_side_assert_count,
        "sync_density": value.sync_density,
    }


def lockstep_outcome_json(outcome: Any) -> dict[str, Any]:
    return {
        "p_head_label": outcome.p_head_label,
        "q_head_label": outcome.q_head_label,
        "success": outcome.success,
        "reason": outcome.reason,
        "coupling_vars": list(outcome.coupling_vars),
        "guard_resolution": outcome.guard_resolution,
        "body_resolution": outcome.body_resolution,
        "preheader_resolution": outcome.preheader_resolution,
        "in_delta": outcome.in_delta,
    }


def egraph_outcome_json(outcome: Any) -> dict[str, Any]:
    return {
        "region": {
            "left_blocks": list(outcome.region.p_blocks),
            "right_blocks": list(outcome.region.q_blocks),
            "live_out": list(outcome.region.live_out),
        },
        "success": outcome.success,
        "reason": outcome.reason,
        "resolution": outcome.resolution,
        "debug_steps": list(getattr(outcome, "debug_steps", []) or []),
    }


def add_trace_pair_comments(text: str, result: Any) -> str:
    comments = trace_pair_comments(result) + egraph_step_comments(result)
    if not comments:
        return text
    return "\n".join(comments) + "\n" + text


def trace_pair_comments(result: Any) -> list[str]:
    comments: list[str] = []
    for outcome in getattr(result, "align_outcomes", []) or []:
        if not getattr(outcome, "success", False):
            continue
        region = outcome.region
        left = ",".join(sorted(region.p_blocks))
        right = ",".join(sorted(region.q_blocks))
        live_out = ",".join(sorted(region.live_out))
        resolution = outcome.resolution or "unknown"
        comments.append(
            "// diffprod.trace_pair "
            f"resolution={resolution} left={left} right={right} live_out={live_out}"
        )
    return comments


def egraph_step_comments(result: Any) -> list[str]:
    comments: list[str] = []
    for outcome in getattr(result, "align_outcomes", []) or []:
        region = outcome.region
        left = ",".join(sorted(region.p_blocks))
        right = ",".join(sorted(region.q_blocks))
        region_text = f"{left}->{right}"
        for index, step in enumerate(getattr(outcome, "debug_steps", []) or []):
            phase = _comment_value(step.get("phase", "unknown"))
            fields = [
                f"region={_comment_value(region_text)}",
                f"index={index}",
                f"phase={phase}",
            ]
            for key in (
                "success",
                "resolution",
                "reason",
                "left_statement_count",
                "right_statement_count",
                "aligned_pair_count",
                "run_steps",
                "command_count",
                "error_type",
                "error",
            ):
                if key in step and step[key] not in (None, ""):
                    fields.append(f"{key}={_comment_value(step[key])}")
            if step.get("phase") == "encode-egglog":
                bindings = step.get("bindings") or {}
                if isinstance(bindings, dict):
                    if "p_term" in bindings:
                        fields.append(f"p_term={_comment_value(bindings['p_term'])}")
                    if "q_term" in bindings:
                        fields.append(f"q_term={_comment_value(bindings['q_term'])}")
                if "check_expr" in step:
                    fields.append(f"check_expr={_comment_value(step['check_expr'])}")
            comments.append("// diffprod.egraph.step " + " ".join(fields))
    return comments


def _comment_value(value: Any) -> str:
    text = str(value).replace("\n", "\\n")
    if len(text) > 240:
        text = text[:237] + "..."
    if any(ch.isspace() for ch in text) or text == "":
        text = '"' + text.replace('"', '\\"') + '"'
    return text


def emit_product_text(program: Any, bpl_emit: Any, ir: Any) -> str:
    text = bpl_emit.emit(program)
    decls = uninterpreted_function_declarations(program, ir)
    if not decls:
        return text
    return "\n".join(decls) + "\n\n" + text


def uninterpreted_function_declarations(program: Any, ir: Any) -> list[str]:
    env = program_type_env(program)
    functions: dict[tuple[str, int], tuple[list[tuple[Any, int]], tuple[Any, int]]] = {}
    for block in program.blocks:
        for stmt in block.stmts:
            collect_stmt_functions(stmt, env, functions, ir)
        if getattr(block, "structured_while", None) is not None:
            collect_expr_functions(
                block.structured_while.guard,
                (ir.Ty.BOOL, 0),
                env,
                functions,
                ir,
            )
            for invariant in block.structured_while.invariants:
                collect_expr_functions(invariant, (ir.Ty.BOOL, 0), env, functions, ir)
            for stmt in block.structured_while.body:
                collect_stmt_functions(stmt, env, functions, ir)
    out: list[str] = []
    for (name, _arity), (args, ret) in sorted(functions.items()):
        arg_decls = ", ".join(
            f"a{index}: {boogie_type(arg_ty, arg_dims, ir)}"
            for index, (arg_ty, arg_dims) in enumerate(args)
        )
        out.append(f"function {name}({arg_decls}) returns ({boogie_type(ret[0], ret[1], ir)});")
    return out


def program_type_env(program: Any) -> dict[str, tuple[Any, int]]:
    env: dict[str, tuple[Any, int]] = {}
    for decl in [*program.params, *program.returns, *program.locals]:
        env[decl.name] = (decl.ty, decl.dims)
    return env


def collect_stmt_functions(
    stmt: Any,
    env: dict[str, tuple[Any, int]],
    functions: dict[tuple[str, int], tuple[list[tuple[Any, int]], tuple[Any, int]]],
    ir: Any,
) -> None:
    if isinstance(stmt, ir.Assign):
        collect_expr_functions(
            stmt.rhs,
            env.get(stmt.lhs, (ir.Ty.INT, 0)),
            env,
            functions,
            ir,
        )
        return
    if isinstance(stmt, ir.ArrayAssign):
        for index in stmt.indices:
            collect_expr_functions(index, (ir.Ty.INT, 0), env, functions, ir)
        collect_expr_functions(stmt.rhs, (ir.Ty.INT, 0), env, functions, ir)
        return
    if isinstance(stmt, (ir.Assume, ir.Assert)):
        collect_expr_functions(stmt.expr, (ir.Ty.BOOL, 0), env, functions, ir)
        return
    if isinstance(stmt, ir.Call):
        for arg in stmt.args:
            collect_expr_functions(arg, None, env, functions, ir)


def collect_expr_functions(
    expr: Any,
    expected: tuple[Any, int] | None,
    env: dict[str, tuple[Any, int]],
    functions: dict[tuple[str, int], tuple[list[tuple[Any, int]], tuple[Any, int]]],
    ir: Any,
) -> None:
    if isinstance(expr, (ir.IntLit, ir.BoolLit, ir.Var)):
        return
    if isinstance(expr, ir.FuncApp):
        arg_types = [infer_expr_type(arg, env, ir) for arg in expr.args]
        key = (expr.name, len(expr.args))
        functions.setdefault(key, (arg_types, expected or (ir.Ty.INT, 0)))
        for arg, arg_type in zip(expr.args, arg_types):
            collect_expr_functions(arg, arg_type, env, functions, ir)
        return
    if isinstance(expr, ir.BinExpr):
        if expr.op in (ir.BinOp.AND, ir.BinOp.OR, ir.BinOp.IMPLIES):
            lhs_expected = rhs_expected = (ir.Ty.BOOL, 0)
        else:
            lhs_expected = rhs_expected = (ir.Ty.INT, 0)
        collect_expr_functions(expr.lhs, lhs_expected, env, functions, ir)
        collect_expr_functions(expr.rhs, rhs_expected, env, functions, ir)
        return
    if isinstance(expr, ir.NotExpr):
        collect_expr_functions(expr.inner, (ir.Ty.BOOL, 0), env, functions, ir)
        return
    if isinstance(expr, ir.IteExpr):
        collect_expr_functions(expr.cond, (ir.Ty.BOOL, 0), env, functions, ir)
        collect_expr_functions(expr.then_, expected, env, functions, ir)
        collect_expr_functions(expr.else_, expected, env, functions, ir)
        return
    if isinstance(expr, ir.ArrayRead):
        collect_expr_functions(expr.base, None, env, functions, ir)
        collect_expr_functions(expr.index, (ir.Ty.INT, 0), env, functions, ir)


def infer_expr_type(expr: Any, env: dict[str, tuple[Any, int]], ir: Any) -> tuple[Any, int]:
    if isinstance(expr, ir.BoolLit):
        return (ir.Ty.BOOL, 0)
    if isinstance(expr, ir.Var):
        return env.get(expr.name, (ir.Ty.INT, 0))
    if isinstance(expr, ir.BinExpr) and expr.op in (
        ir.BinOp.EQ,
        ir.BinOp.NEQ,
        ir.BinOp.LT,
        ir.BinOp.LE,
        ir.BinOp.GT,
        ir.BinOp.GE,
        ir.BinOp.AND,
        ir.BinOp.OR,
        ir.BinOp.IMPLIES,
    ):
        return (ir.Ty.BOOL, 0)
    if isinstance(expr, ir.NotExpr):
        return (ir.Ty.BOOL, 0)
    if isinstance(expr, ir.IteExpr):
        return infer_expr_type(expr.then_, env, ir)
    return (ir.Ty.INT, 0)


def boogie_type(ty: Any, dims: int, ir: Any) -> str:
    if ty == ir.Ty.BOOL:
        return "bool"
    if ty == ir.Ty.INT_MAP:
        if dims <= 0:
            dims = 1
        return f"[{', '.join(['int'] * dims)}]int"
    return "int"


def ensure_diffprod_package_on_path() -> bool:
    """Locate the relational-product library.

    The package was renamed from ``diffprod`` to ``deltarel``. Try the new
    name first, then fall back to the legacy name. Re-exports under the
    ``diffprod`` alias when only ``deltarel`` is present, so the rest of
    the codebase can keep importing ``diffprod.product_v2`` unchanged.
    """
    explicit_root = os.environ.get("SMACK_DELTAREL_ROOT")
    candidate_roots: list[Path] = []
    if explicit_root:
        candidate_roots.append(Path(explicit_root))

    here = Path(__file__).resolve()
    for parent in here.parents:
        candidate_roots.append(parent / "external" / "deltarel")

    for root in candidate_roots:
        if not (root / "deltarel" / "product_v2.py").exists():
            continue
        package_root = str(root)
        if package_root not in sys.path:
            sys.path.insert(0, package_root)

    for name in ("diffprod", "deltarel"):
        try:
            module = __import__(name + ".product_v2", fromlist=["product_v2"])
        except ImportError:
            sys.modules.pop(name, None)
            continue
        if name == "deltarel":
            sys.modules["diffprod"] = sys.modules["deltarel"]
            sys.modules["diffprod.product_v2"] = module
        return True

    for parent in here.parents:
        for pkg_name in ("diffprod", "deltarel"):
            candidate = parent / pkg_name / pkg_name / "product_v2.py"
            if not candidate.exists():
                continue
            package_root = str(parent / pkg_name)
            if package_root not in sys.path:
                sys.path.insert(0, package_root)
            try:
                module = __import__(pkg_name + ".product_v2", fromlist=["product_v2"])
            except ImportError:
                sys.modules.pop(pkg_name, None)
                continue
            if pkg_name == "deltarel":
                sys.modules["diffprod"] = sys.modules["deltarel"]
                sys.modules["diffprod.product_v2"] = module
            return True
    return False


def emit_metadata_product(
    left: ParsedBoogieProgram,
    right: ParsedBoogieProgram,
    impact: ImpactResult,
    summaries: SummaryPlan,
) -> str:
    lines: list[str] = [
        "// generated by SMACK diff-product",
        "// This artifact records the impacted Boogie cut and summary regions.",
        "",
        "procedure smack_diff_product_metadata();",
        "implementation smack_diff_product_metadata()",
        "{",
        "entry:",
        '  assume {:diff.product "metadata"} true;',
    ]
    for side, parsed, impacted in (
        ("left", left, impact.left),
        ("right", right, impact.right),
    ):
        for block_id in sorted(impacted.impacted_blocks):
            label = parsed.provenance.block_labels.get(block_id, block_id)
            lines.append(
                "  assume "
                f'{{:diff.impacted "{_bpl_string(side)}" "{_bpl_string(block_id)}" '
                f'"{_bpl_string(label)}"}} true;'
            )
        for stmt_id in sorted(impacted.impacted_statements):
            lines.append(
                "  assume "
                f'{{:diff.impacted.stmt "{_bpl_string(side)}" '
                f'"{_bpl_string(stmt_id)}"}} true;'
            )
    for side, regions in (("left", summaries.left), ("right", summaries.right)):
        for region in regions:
            eq = region.equivalent_to or ""
            lines.append(
                "  assume "
                f'{{:diff.summary "{_bpl_string(side)}" '
                f'"{_bpl_string(region.block_id)}" "{_bpl_string(eq)}"}} true;'
            )
    lines.extend(["  return;", "}", ""])
    return "\n".join(lines)


def _bpl_string(value: str) -> str:
    return (
        value.replace("\\", "\\\\")
        .replace('"', '\\"')
        .replace("\n", "\\n")
        .replace("\r", "\\r")
        .replace("\t", "\\t")
    )

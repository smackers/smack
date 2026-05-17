"""SMACK-native diff/product support.

Re-exports the orchestration entry point so callers can write
`from smack.diffprod import run_diff_product` without descending into
the sub-module layout.
"""

from __future__ import annotations

from .orchestrate import (
    diff_product_patched_filename,
    diff_product_side_args,
    llvm_to_bpl_option_args,
    run_diff_product,
    run_paired_diff_product_lowering,
    verify_diff_product,
)

__all__ = [
    "diff_product_patched_filename",
    "diff_product_side_args",
    "llvm_to_bpl_option_args",
    "run_diff_product",
    "run_paired_diff_product_lowering",
    "verify_diff_product",
]

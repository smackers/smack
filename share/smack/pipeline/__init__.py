"""smack.pipeline — language frontends + LLVM-to-Boogie translation.

Re-exports the public entry points for each pipeline stage.
"""

from __future__ import annotations

from .frontend import frontend, target_selection
from .transform import transform_bpl, transform_out

__all__ = [
    "frontend",
    "target_selection",
    "transform_bpl",
    "transform_out",
]

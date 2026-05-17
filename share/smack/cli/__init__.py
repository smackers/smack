"""smack.cli — argparse + verification-result enums.

Re-exports the public surface so `from smack.cli import VResult` works
without importing the parser module (which itself imports the heavier
pipeline graph).
"""

from __future__ import annotations

from .results import PropertyAction, VProperty, VResult

__all__ = ["PropertyAction", "VProperty", "VResult"]

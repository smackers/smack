"""SV-COMP integration: portfolio driver + result XML emission.

Lazy attribute access — utils imports smack.top which itself reaches
back into svcomp.utils, so an eager `from .utils import ...` here
creates a circular import. PEP 562 __getattr__ defers the lookup
until the symbol is actually requested.
"""

from __future__ import annotations

from typing import Any

__all__ = ["verify_bpl_svcomp"]


def __getattr__(name: str) -> Any:
    if name == "verify_bpl_svcomp":
        from .utils import verify_bpl_svcomp

        return verify_bpl_svcomp
    raise AttributeError(f"module 'smack.svcomp' has no attribute {name!r}")

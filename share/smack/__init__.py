"""SMACK Python driver package.

This package wraps the C++ ``llvm2bpl`` translator and the back-end
verifiers (Boogie, Corral) behind the ``smack`` CLI entry point.

Public surface re-exported here is intentionally small:

* ``__version__`` — same string as ``share/smack/constants.py`` (single
  source of truth, also resolved at build time by ``pyproject.toml``
  via hatch and by ``CMakeLists.txt`` via ``file(STRINGS ...)``).
* ``main`` — CLI entry point; ``[project.scripts] smack = "smack.top:main"``.
* ``VResult`` / ``VProperty`` — verification result enums consumed by
  programmatic callers.

Internal modules (``cli``, ``pipeline``, ``verifier``, ``diffprod``,
``svcomp``) are importable but not part of the stable public API. They
move and split as the Phase 4 modernization progresses.
"""

from __future__ import annotations

from .cli.results import VProperty, VResult
from .constants import VERSION as __version__

__all__ = ["__version__", "VResult", "VProperty", "main"]


def main() -> None:
    """Lazy entry point so importing ``smack`` doesn't pull the whole
    translator/verifier import graph until the CLI actually runs.

    Equivalent to ``from smack.top import main; main()``.
    """
    from .top import main as _main

    _main()

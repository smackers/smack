"""Centralized logging configuration for SMACK.

Phase B3 of the modernization plan introduced a `smack` logger hierarchy so
warnings/debug output is filterable via standard Python logging instead of
ad-hoc print() calls. User-facing stdout contract messages (e.g. "SMACK found
no errors with unroll bound N") stay on print() because regression tests
grep for them.

Levels by verbosity flag:
- `--quiet`  → WARNING (errors + warnings only)
- default    → INFO    (normal output)
- `--verbose`→ INFO with console handler
- `--debug`  → DEBUG   (everything)
- `--warn=silent` suppresses `smack.warnings` sub-logger
"""

from __future__ import annotations

import logging
import sys

_ROOT_LOGGER_NAME = "smack"
_WARNINGS_LOGGER_NAME = "smack.warnings"

_FORMATTER = logging.Formatter("%(levelname)s [smack] %(message)s")


def get_logger(name: str | None = None) -> logging.Logger:
    """Return a child logger under the `smack` hierarchy."""
    if name is None:
        return logging.getLogger(_ROOT_LOGGER_NAME)
    return logging.getLogger(f"{_ROOT_LOGGER_NAME}.{name}")


def get_warnings_logger() -> logging.Logger:
    """Logger for `--warn=silent`-suppressible warnings."""
    return logging.getLogger(_WARNINGS_LOGGER_NAME)


def configure(
    *,
    quiet: bool = False,
    verbose: bool = False,
    debug: bool = False,
    warn: str = "approximate",
) -> None:
    """Wire root smack logger based on argparse flags from arguments()."""
    root = logging.getLogger(_ROOT_LOGGER_NAME)

    # Wipe handlers in case configure() is called twice (e.g. in tests).
    for h in list(root.handlers):
        root.removeHandler(h)

    if debug:
        level = logging.DEBUG
    elif quiet:
        level = logging.WARNING
    else:
        level = logging.INFO

    handler = logging.StreamHandler(sys.stderr)
    handler.setFormatter(_FORMATTER)
    root.addHandler(handler)
    root.setLevel(level)

    # `--warn=silent` mutes the warnings sub-logger irrespective of overall level.
    warnings_logger = logging.getLogger(_WARNINGS_LOGGER_NAME)
    if warn == "silent":
        warnings_logger.setLevel(logging.CRITICAL + 1)
    else:
        warnings_logger.setLevel(logging.NOTSET)  # inherit from root

    # `--verbose` enabled an explicit INFO handler — already covered above.
    _ = verbose  # reserved for future per-module verbosity gating

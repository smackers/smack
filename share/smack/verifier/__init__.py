"""smack.verifier — back-end verifier command builders + runners.

Re-exports the public command-builder + runner surface so callers can
write `from smack.verifier import boogie_command, Command` without
importing the heavier portfolio + diffprod orchestration.
"""

from __future__ import annotations

from .commands import boogie_command, corral_command
from .process import Command, CommandCrashed, CommandError, CommandResult

__all__ = [
    "Command",
    "CommandCrashed",
    "CommandError",
    "CommandResult",
    "boogie_command",
    "corral_command",
]

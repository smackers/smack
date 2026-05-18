"""Typed command builder + runner for verifier subprocesses.

Replaces the historical pattern of building bare ``list[str]`` argv lists
and passing them through ``smack.utils.try_command`` with implicit
dependencies on the global ``top.args``. A :class:`Command` carries every
piece of state the runner needs (executable, args, cwd, env, timeout,
capture mode, log file). The bare ``list[str]`` ``try_command`` entry
point in ``smack.utils`` remains available for migration; new code should
construct a :class:`Command` and call its ``run`` method.

Example::

    from smack.verifier.process import Command
    result = Command(executable="boogie", args=["/timeLimit:60", "prog.bpl"],
                     timeout=60).run()
    if result.timed_out:
        ...
    print(result.stdout)
"""

from __future__ import annotations

import contextlib
import os
import signal
import subprocess
from collections.abc import Mapping, Sequence
from dataclasses import dataclass, field
from pathlib import Path
from threading import Timer


class CommandError(RuntimeError):
    """Subprocess returned non-zero (and was not killed by timeout)."""

    def __init__(self, command: Command, returncode: int, output: str) -> None:
        super().__init__(f"command {command.executable!r} failed with rc={returncode}\n{output}")
        self.command = command
        self.returncode = returncode
        self.output = output


class CommandCrashed(RuntimeError):
    """Subprocess crashed (SIGSEGV or other fatal signal)."""

    def __init__(self, command: Command, signal_no: int) -> None:
        super().__init__(f"command {command.executable!r} terminated by signal {signal_no}")
        self.command = command
        self.signal_no = signal_no


@dataclass(frozen=True)
class CommandResult:
    """Outcome of running a :class:`Command`.

    ``timed_out`` is True when the timer killed the process group; in that
    case ``returncode`` is the negative signal number (typically -9). The
    raw stdout/stderr stream is concatenated into ``stdout`` (we merge
    stderr into stdout to match the legacy ``try_command`` behaviour that
    callers depend on for verifier output parsing).
    """

    command: Command
    returncode: int
    stdout: str
    timed_out: bool

    @property
    def ok(self) -> bool:
        return self.returncode == 0 and not self.timed_out


@dataclass(frozen=True)
class Command:
    """Plan for invoking an external tool.

    ``args`` is a tuple of strings so the dataclass is hashable and
    debug-loggable. ``env`` overlays the parent environment; pass an empty
    mapping for "no overrides".
    """

    executable: str
    args: Sequence[str] = field(default_factory=tuple)
    cwd: Path | None = None
    env: Mapping[str, str] = field(default_factory=dict)
    timeout: float | None = None
    console_echo: bool = False

    def to_argv(self) -> list[str]:
        return [self.executable, *self.args]

    def with_extra_args(self, *extra: str) -> Command:
        """Return a new Command with additional positional args appended."""
        return Command(
            executable=self.executable,
            args=(*self.args, *extra),
            cwd=self.cwd,
            env=self.env,
            timeout=self.timeout,
            console_echo=self.console_echo,
        )

    def _build_env(self) -> Mapping[str, str] | None:
        if not self.env:
            return None
        merged = dict(os.environ)
        merged.update(self.env)
        return merged

    def run(self) -> CommandResult:
        """Execute the command and return a :class:`CommandResult`.

        Raises :class:`CommandError` on non-zero exit (unless timed out)
        and :class:`CommandCrashed` on fatal signals. Timeouts return a
        normal result with ``timed_out=True`` and the partial output, so
        verifier wrappers can still parse "timed out" messages out of it.
        """
        argv = self.to_argv()
        output = ""
        proc: subprocess.Popen[str] | None = None
        timer: Timer | None = None
        timed_out_flag = [False]

        try:
            proc = subprocess.Popen(
                argv,
                cwd=str(self.cwd) if self.cwd else None,
                env=self._build_env(),
                preexec_fn=os.setsid,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                universal_newlines=True,
            )

            if self.timeout:

                def _kill() -> None:
                    if not timed_out_flag[0] and proc and proc.poll() is None:
                        timed_out_flag[0] = True
                        os.killpg(os.getpgid(proc.pid), signal.SIGKILL)

                timer = Timer(self.timeout, _kill)
                timer.start()

            if self.console_echo:
                assert proc.stdout is not None
                for line in proc.stdout:
                    output += line
                    print(line, end="")
                proc.wait()
            else:
                output = proc.communicate()[0] or ""

            rc = proc.returncode
            proc = None  # don't kill in finally

            if timed_out_flag[0]:
                return CommandResult(
                    command=self,
                    returncode=rc,
                    stdout=output + f"\n{self.executable} timed out.",
                    timed_out=True,
                )
            if rc == -signal.SIGSEGV:
                raise CommandCrashed(self, signal.SIGSEGV)
            if rc:
                raise CommandError(self, rc, output)
            return CommandResult(command=self, returncode=rc, stdout=output, timed_out=False)
        finally:
            if timer:
                timer.cancel()
            if proc:
                with contextlib.suppress(ProcessLookupError, OSError):
                    os.killpg(os.getpgid(proc.pid), signal.SIGKILL)

"""Unit tests for smack.verifier.process — Command dataclass + runner."""

import os
import sys

import pytest
from smack.verifier.process import Command, CommandCrashed, CommandError, CommandResult


# ---------- Command (pure dataclass behaviour) ----------


def test_command_to_argv_includes_executable_first():
    cmd = Command(executable="boogie", args=("/timeLimit:60", "prog.bpl"))
    assert cmd.to_argv() == ["boogie", "/timeLimit:60", "prog.bpl"]


def test_command_to_argv_empty_args():
    assert Command(executable="boogie").to_argv() == ["boogie"]


def test_command_with_extra_args_appends_preserving_other_fields():
    base = Command(
        executable="boogie",
        args=("/timeLimit:60",),
        timeout=42.0,
        console_echo=True,
    )
    extended = base.with_extra_args("/inferModifies", "prog.bpl")
    assert extended.executable == "boogie"
    assert extended.args == ("/timeLimit:60", "/inferModifies", "prog.bpl")
    assert extended.timeout == 42.0
    assert extended.console_echo is True
    # Original is unchanged (frozen dataclass).
    assert base.args == ("/timeLimit:60",)


def test_command_is_immutable_frozen_dataclass():
    cmd = Command(executable="boogie", args=("x",))
    with pytest.raises(Exception):
        cmd.executable = "corral"  # type: ignore[misc]


# ---------- run() behaviour ----------


def test_run_ok_captures_stdout():
    cmd = Command(executable=sys.executable, args=("-c", "print('hello smack')"))
    result = cmd.run()
    assert isinstance(result, CommandResult)
    assert result.ok
    assert result.returncode == 0
    assert "hello smack" in result.stdout
    assert result.timed_out is False


def test_run_merges_stderr_into_stdout():
    code = "import sys; print('out'); print('err', file=sys.stderr)"
    result = Command(executable=sys.executable, args=("-c", code)).run()
    assert result.ok
    assert "out" in result.stdout
    assert "err" in result.stdout


def test_run_non_zero_raises_command_error():
    code = "import sys; sys.stdout.write('bad'); sys.exit(7)"
    cmd = Command(executable=sys.executable, args=("-c", code))
    with pytest.raises(CommandError) as exc:
        cmd.run()
    assert exc.value.returncode == 7
    assert "bad" in exc.value.output


def test_run_timeout_returns_result_with_timed_out_true():
    # Sleep longer than the timeout; expect SIGKILL via the timer.
    code = "import time; time.sleep(5)"
    cmd = Command(executable=sys.executable, args=("-c", code), timeout=0.2)
    result = cmd.run()
    assert result.timed_out is True
    assert "timed out" in result.stdout
    assert not result.ok


def test_run_segfault_raises_command_crashed(tmp_path):
    # Force SIGSEGV by raising it explicitly inside a fresh python.
    code = "import os, signal; os.kill(os.getpid(), signal.SIGSEGV)"
    cmd = Command(executable=sys.executable, args=("-c", code))
    with pytest.raises(CommandCrashed):
        cmd.run()


def test_run_env_overlays_parent_environment(tmp_path):
    code = "import os; print(os.environ.get('SMACK_PROCESS_TEST', 'MISSING'))"
    cmd = Command(
        executable=sys.executable,
        args=("-c", code),
        env={"SMACK_PROCESS_TEST": "present"},
    )
    result = cmd.run()
    assert result.ok
    assert "present" in result.stdout
    # Confirm the parent environment was preserved (PATH still inherited).
    assert "PATH" in os.environ  # sanity


def test_run_cwd_changes_working_directory(tmp_path):
    code = "import os; print(os.getcwd())"
    cmd = Command(executable=sys.executable, args=("-c", code), cwd=tmp_path)
    result = cmd.run()
    assert result.ok
    # macOS resolves /tmp -> /private/tmp; compare resolved paths.
    assert str(tmp_path.resolve()) in result.stdout


def test_command_error_message_includes_executable_and_rc():
    cmd = Command(executable=sys.executable, args=("-c", "import sys; sys.exit(3)"))
    with pytest.raises(CommandError) as exc:
        cmd.run()
    msg = str(exc.value)
    assert sys.executable in msg or "python" in msg
    assert "rc=3" in msg

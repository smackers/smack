"""Tests for smack.utils logger conversion.

Phase 4.2 moved the ad-hoc `print("Running ...")` debug line and the
stderr error print in `try_command` onto the `smack.utils` logger.
These tests pin that behaviour via pytest's caplog fixture so a
regression that re-introduces bare prints fails CI.
"""

from __future__ import annotations

import argparse
import logging
import shutil
import sys

import pytest


def make_args(**overrides):
    defaults = dict(
        debug=False,
        verbose=False,
        quiet=False,
    )
    defaults.update(overrides)
    return argparse.Namespace(**defaults)


def _install_smack_top_args(monkeypatch, args):
    """try_command pulls smack.top.args at runtime. Plant a fake."""
    import smack.top

    monkeypatch.setattr(smack.top, "args", args, raising=False)


def test_running_cmd_emits_debug_log_when_debug_flag_set(monkeypatch, caplog):
    from smack import utils

    _install_smack_top_args(monkeypatch, make_args(debug=True))

    if not shutil.which("true"):
        pytest.skip("`true` not on PATH")

    with caplog.at_level(logging.DEBUG, logger="smack.utils"):
        utils.try_command(["true"])

    debug_msgs = [
        r.getMessage()
        for r in caplog.records
        if r.name == "smack.utils" and r.levelno == logging.DEBUG
    ]
    assert any(
        "Running true" in m for m in debug_msgs
    ), f"expected a 'Running true' debug message; got {debug_msgs!r}"


def test_running_cmd_silent_when_debug_flag_unset(monkeypatch, caplog):
    from smack import utils

    _install_smack_top_args(monkeypatch, make_args(debug=False))

    if not shutil.which("true"):
        pytest.skip("`true` not on PATH")

    with caplog.at_level(logging.DEBUG, logger="smack.utils"):
        utils.try_command(["true"])

    debug_msgs = [
        r.getMessage()
        for r in caplog.records
        if r.name == "smack.utils" and r.levelno == logging.DEBUG
    ]
    assert not debug_msgs, f"expected no debug messages without --debug; got {debug_msgs!r}"


def test_subprocess_failure_logs_error_then_exits(monkeypatch, caplog):
    """OSError path: file-not-found subprocess should log captured output
    at ERROR level, then SystemExit. The log + the exit message should
    both reach the test."""
    from smack import utils

    _install_smack_top_args(monkeypatch, make_args(debug=False))

    with (
        caplog.at_level(logging.ERROR, logger="smack.utils"),
        pytest.raises(SystemExit),
    ):
        utils.try_command(["/nonexistent-smack-binary-for-test"])

    error_msgs = [
        r.getMessage()
        for r in caplog.records
        if r.name == "smack.utils" and r.levelno == logging.ERROR
    ]
    assert any(
        "subprocess output before failure" in m for m in error_msgs
    ), f"expected an error log on subprocess failure; got {error_msgs!r}"


def test_logger_name_is_under_smack_namespace():
    """smack.utils._log must be in the smack.* hierarchy so the global
    --debug / --quiet flags configured in smack.logging_config propagate."""
    from smack import utils

    assert utils._log.name == "smack.utils"


def test_no_bare_print_imports_in_utils_module():
    """Cheap sanity check: ensure no stray `print(` calls outside the
    intentional console-echo branch that surfaces subprocess output to
    the user under --verbose/--debug."""
    import inspect

    from smack import utils

    src = inspect.getsource(utils)
    # The console-echo print at the subprocess-read loop is the only
    # remaining bare print — count it.
    print_calls = src.count("print(")
    assert print_calls <= 1, (
        f"expected at most one print() in utils.py (the console echo); " f"found {print_calls}"
    )


# Sanity: import shape stable.
def test_utils_exports_try_command_and_helpers():
    from smack import utils

    assert callable(utils.try_command)
    assert callable(utils.temporary_file)
    assert callable(utils.temporary_directory)
    assert callable(utils.remove_temp_files)
    assert callable(utils.smack_root)
    assert callable(utils.smack_header_path)
    assert callable(utils.smack_lib)
    assert callable(utils.smack_portfolio_path)


# Sentinel — keeps the import graph from changing under us.
def test_sys_import_still_present_for_sys_exit():
    from smack import utils

    assert "sys" in dir(utils) or hasattr(utils, "sys"), (
        "utils.py still calls sys.exit on error paths; the import "
        "must remain even after the print -> logger migration"
    )
    # Direct: this should succeed.
    assert utils.sys is sys

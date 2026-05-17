"""Unit tests for smack.verifier.commands."""

import argparse

import pytest
from smack.verifier.commands import (
    boogie_command,
    corral_command,
)


def make_args(**overrides):
    defaults = dict(
        time_limit=120,
        max_violations=1,
        modular=False,
        unroll=4,
        solver="z3",
        bpl_file="prog.bpl",
        context_bound=2,
        loop_limit=10,
        entry_points=["main"],
    )
    defaults.update(overrides)
    return argparse.Namespace(**defaults)


# --- boogie ---


def test_boogie_command_basic():
    cmd = boogie_command(make_args())
    assert cmd[0] == "boogie"
    assert "/inferModifies" in cmd
    assert "/timeLimit:120" in cmd
    assert "/errorLimit:1" in cmd
    assert "/loopUnroll:4" in cmd


def test_boogie_command_modular_skips_unroll():
    cmd = boogie_command(make_args(modular=True))
    assert all(not c.startswith("/loopUnroll") for c in cmd)


def test_boogie_command_emits_no_solver_override_by_default():
    # CVC4 / Yices2 support was dropped in Phase 1; Z3 is the only solver
    # and Boogie picks it without an explicit /proverOpt:SOLVER flag.
    cmd = boogie_command(make_args())
    assert all(not c.startswith("/proverOpt:SOLVER=") for c in cmd)


# --- corral ---


def test_corral_command_basic():
    cmd = corral_command(make_args())
    assert cmd[0] == "corral"
    assert cmd[1] == "prog.bpl"
    assert "/k:2" in cmd
    assert "/maxStaticLoopBound:10" in cmd
    assert "/recursionBound:4" in cmd


def test_corral_command_emits_no_solver_override_by_default():
    cmd = corral_command(make_args())
    assert all(not c.startswith("/bopt:proverOpt:SOLVER=") for c in cmd)


@pytest.mark.parametrize(
    "builder,first",
    [(boogie_command, "boogie"), (corral_command, "corral")],
)
def test_command_first_token_is_binary_name(builder, first):
    assert builder(make_args())[0] == first

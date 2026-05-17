"""Unit tests for smack.pipeline.transform."""

import argparse
import shutil

import pytest
from smack.pipeline.transform import transform_bpl, transform_out


def make_args(**overrides):
    defaults = dict(transform_bpl=None, transform_out=None, bpl_file=None)
    defaults.update(overrides)
    return argparse.Namespace(**defaults)


# --- transform_out ---


def test_transform_out_passthrough_when_none():
    assert transform_out(make_args(transform_out=None), "hello") == "hello"


def test_transform_out_invokes_subprocess():
    if not shutil.which("cat"):
        pytest.skip("cat unavailable")
    out = transform_out(make_args(transform_out="cat"), "boogie text\n")
    assert out == "boogie text\n"


def test_transform_out_runs_tr_uppercase():
    if not shutil.which("tr"):
        pytest.skip("tr unavailable")
    out = transform_out(make_args(transform_out="tr a-z A-Z"), "smack")
    assert out == "SMACK"


# --- transform_bpl ---


def test_transform_bpl_noop_when_none(tmp_path):
    bpl = tmp_path / "t.bpl"
    original = "axiom true;\n"
    bpl.write_text(original)
    transform_bpl(make_args(bpl_file=str(bpl), transform_bpl=None))
    assert bpl.read_text() == original


def test_transform_bpl_rewrites_file_in_place(tmp_path):
    if not shutil.which("tr"):
        pytest.skip("tr unavailable")
    bpl = tmp_path / "u.bpl"
    bpl.write_text("axiom true;")
    transform_bpl(make_args(bpl_file=str(bpl), transform_bpl="tr a-z A-Z"))
    assert bpl.read_text() == "AXIOM TRUE;"


def test_transform_bpl_passes_old_content_to_stdin(tmp_path):
    if not shutil.which("cat"):
        pytest.skip("cat unavailable")
    bpl = tmp_path / "v.bpl"
    body = "var x: int;\nprocedure main() { x := 0; }\n"
    bpl.write_text(body)
    transform_bpl(make_args(bpl_file=str(bpl), transform_bpl="cat"))
    assert bpl.read_text() == body

"""Tests for tools/boogie_normalize.py.

Pins the canonicalizer's behavior so the Phase 2 sea-dsa NewPM port
audit catches real Boogie divergences without flagging cosmetic ones."""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

_REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(_REPO_ROOT))

from tools.boogie_normalize import canonicalize, diff_files, main  # noqa: E402


# ---------- comment stripping ----------


def test_line_comments_removed():
    src = "var $x: int; // generated 2026-05-17 by SmackInstGenerator\n"
    out = canonicalize(src)
    assert "//" not in out
    assert "var $x: int;" in out


def test_block_comments_removed():
    src = "var /* old name was $y */ $x: int;\n"
    out = canonicalize(src)
    assert "/*" not in out
    assert "$x: int" in out


# ---------- variable suffix normalization ----------


def test_var_suffix_collapsed_to_N():
    a = canonicalize("var $tmp.1: int;\n")
    b = canonicalize("var $tmp.42: int;\n")
    assert a == b
    assert "$tmp.N" in a


def test_distinct_base_names_still_diverge():
    a = canonicalize("var $tmp.1: int;\n")
    b = canonicalize("var $other.1: int;\n")
    assert a != b


def test_suffix_only_on_dollar_prefixed_identifiers():
    # User identifiers without `$` are not touched.
    src = "var user_var.1: int;\n"
    out = canonicalize(src)
    assert "user_var.1" in out
    assert "user_var.N" not in out


# ---------- attribute arg sorting ----------


def test_attr_args_sorted_alphabetically():
    a = canonicalize("assert {:attr c, a, b} true;\n")
    b = canonicalize("assert {:attr a, b, c} true;\n")
    assert a == b
    assert "{:attr a, b, c}" in a


def test_attr_with_single_arg_unchanged():
    out = canonicalize("assert {:attr only} true;\n")
    assert "{:attr only}" in out


def test_attr_name_preserved():
    out = canonicalize("assert {:foo b, a} true;\n")
    assert "{:foo a, b}" in out
    assert "{:bar" not in out


# ---------- blank line collapse ----------


def test_multiple_blank_lines_collapsed_to_one():
    src = "var $a: int;\n\n\n\nvar $b: int;\n"
    out = canonicalize(src)
    # At most one blank line between non-blank lines.
    assert "\n\n\n" not in out
    assert "$a" in out and "$b" in out


def test_trailing_whitespace_stripped():
    src = "var $a: int;   \nvar $b: int;\t\n"
    out = canonicalize(src)
    for line in out.splitlines():
        assert line == line.rstrip()


# ---------- idempotence ----------


@pytest.mark.parametrize(
    "src",
    [
        "var $tmp.1: int;\nassert {:attr c, a} true;\n// comment\n",
        "procedure foo() {\n  havoc $x.7;\n  assert {:loop 1, 2, 3} true;\n}\n",
        "",
        "\n\n\n",
    ],
)
def test_canonicalize_is_idempotent(src):
    once = canonicalize(src)
    twice = canonicalize(once)
    assert once == twice


def test_trailing_newline_always_present():
    assert canonicalize("var $x: int;").endswith("\n")
    assert canonicalize("var $x: int;\n").endswith("\n")
    assert canonicalize("").endswith("\n") or canonicalize("") == ""


# ---------- diff_files ----------


def test_diff_files_empty_on_canonically_equal_input(tmp_path):
    left = tmp_path / "a.bpl"
    right = tmp_path / "b.bpl"
    left.write_text("var $x.1: int; // hello\n")
    right.write_text("var $x.7: int;\n")
    diff = diff_files(left, right)
    assert diff == []


def test_diff_files_reports_real_divergence(tmp_path):
    left = tmp_path / "a.bpl"
    right = tmp_path / "b.bpl"
    left.write_text("var $x: int;\n")
    right.write_text("var $y: int;\n")
    diff = diff_files(left, right)
    assert diff != []
    joined = "".join(diff)
    assert "$x" in joined
    assert "$y" in joined


# ---------- CLI main ----------


def test_cli_exit_zero_on_match(tmp_path, capsys):
    left = tmp_path / "a.bpl"
    right = tmp_path / "b.bpl"
    left.write_text("var $tmp.1: int;\n")
    right.write_text("var $tmp.5: int;\n")
    rc = main([str(left), str(right)])
    assert rc == 0
    out = capsys.readouterr().out
    assert "OK" in out


def test_cli_exit_nonzero_on_drift(tmp_path, capsys):
    left = tmp_path / "a.bpl"
    right = tmp_path / "b.bpl"
    left.write_text("var $a: int;\n")
    right.write_text("var $b: int;\n")
    rc = main([str(left), str(right)])
    assert rc == 1
    out = capsys.readouterr().out
    assert "FAIL" in out


def test_cli_quiet_suppresses_diff(tmp_path, capsys):
    left = tmp_path / "a.bpl"
    right = tmp_path / "b.bpl"
    left.write_text("var $a: int;\n")
    right.write_text("var $b: int;\n")
    rc = main([str(left), str(right), "--quiet"])
    assert rc == 1
    out = capsys.readouterr().out
    # No unified-diff hunk header — just the FAIL line.
    assert "@@" not in out
    assert "FAIL" in out

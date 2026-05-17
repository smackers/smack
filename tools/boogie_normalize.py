"""Boogie source canonicalizer for cross-pipeline diffs.

Phase 2 (sea-dsa NewPM port) needs a corpus equivalence audit: the
old legacy-PM pipeline and the new NewPM pipeline must produce
identical-behavior Boogie. Byte-identical output is rare in practice
because:

* Variable suffixes (`$tmp.1` vs `$tmp.2`) drift with pass ordering.
* `{:attr a, b}` attribute argument order is set-like.
* Comments include timestamps + transient pass names.
* Trailing whitespace, empty lines.

This module turns a `.bpl` file into a canonical form that's stable
under those nuisance differences while still flagging real semantic
divergence (different procedures, different assertions, different
modifies sets).

CLI:

    python3 -m tools.boogie_normalize a.bpl b.bpl
        prints a unified diff of the canonical forms; exit 1 on drift.

API:

    from tools.boogie_normalize import canonicalize, diff_files
    canonical_text = canonicalize(open("file.bpl").read())
    list_of_unified_diff_lines = diff_files("a.bpl", "b.bpl")
"""

from __future__ import annotations

import argparse
import difflib
import re
import sys
from pathlib import Path
from typing import Iterable, List

# Match SMACK's generated variable-suffix pattern: `$<word>.<digits>`.
# We strip the numeric suffix so `$tmp.1` and `$tmp.7` compare equal —
# but keep the base name so `$tmp` vs `$other` still diverges.
_VAR_SUFFIX_RE = re.compile(r"(\$[A-Za-z_][A-Za-z_0-9]*)\.\d+")

# Match a Boogie attribute: `{:name a, b, c}`. We re-emit the args in
# sorted order so attribute permutations match.
_ATTR_RE = re.compile(r"\{:([A-Za-z_][A-Za-z_0-9]*)\s+([^{}]+?)\}")

# Boogie line comments — strip entirely so timestamps + transient
# pass names don't pollute the diff.
_LINE_COMMENT_RE = re.compile(r"//.*$")

# `/* ... */` block comments — single-line variant. Multi-line block
# comments aren't used by SMACK output today; keep this conservative.
_BLOCK_COMMENT_RE = re.compile(r"/\*.*?\*/")


def _strip_comments(text: str) -> str:
    text = _BLOCK_COMMENT_RE.sub("", text)
    text = _LINE_COMMENT_RE.sub("", text)
    return text


def _normalize_var_suffixes(text: str) -> str:
    return _VAR_SUFFIX_RE.sub(r"\1.N", text)


def _normalize_attr_args(match: "re.Match[str]") -> str:
    name = match.group(1)
    raw_args = match.group(2)
    # Split on commas + strip; sort.
    parts = [p.strip() for p in raw_args.split(",") if p.strip()]
    parts.sort()
    return "{:" + name + " " + ", ".join(parts) + "}"


def _normalize_attrs(text: str) -> str:
    return _ATTR_RE.sub(_normalize_attr_args, text)


def _collapse_blank_lines(text: str) -> str:
    out: List[str] = []
    blank_run = 0
    for line in text.splitlines():
        stripped = line.rstrip()
        if not stripped:
            blank_run += 1
            if blank_run <= 1:
                out.append("")
        else:
            blank_run = 0
            out.append(stripped)
    return "\n".join(out)


def canonicalize(text: str) -> str:
    """Return a canonical form of `.bpl` source.

    Idempotent — `canonicalize(canonicalize(x)) == canonicalize(x)`.
    """
    text = _strip_comments(text)
    text = _normalize_attrs(text)
    text = _normalize_var_suffixes(text)
    text = _collapse_blank_lines(text)
    # Ensure trailing newline so file-end diffs don't show `\ No newline...`
    if not text.endswith("\n"):
        text += "\n"
    return text


def diff_files(left: str | Path, right: str | Path) -> List[str]:
    """Return a list of unified-diff lines between the canonicalized
    forms of two `.bpl` files. Empty list means no drift."""
    left_path = Path(left)
    right_path = Path(right)
    a = canonicalize(left_path.read_text()).splitlines(keepends=True)
    b = canonicalize(right_path.read_text()).splitlines(keepends=True)
    return list(
        difflib.unified_diff(
            a, b, fromfile=str(left_path), tofile=str(right_path), n=3
        )
    )


def main(argv: Iterable[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Diff two Boogie source files after canonicalization."
    )
    parser.add_argument("left", type=Path, help="first .bpl file")
    parser.add_argument("right", type=Path, help="second .bpl file")
    parser.add_argument(
        "--quiet",
        action="store_true",
        help="only print verdict, not the diff",
    )
    args = parser.parse_args(list(argv) if argv is not None else None)

    diff = diff_files(args.left, args.right)
    if not diff:
        if not args.quiet:
            print(f"OK: {args.left} matches {args.right} after canonicalization")
        return 0

    if args.quiet:
        print(f"FAIL: {args.left} diverges from {args.right}")
    else:
        sys.stdout.writelines(diff)
        print(f"\nFAIL: {len(diff)} line(s) of drift")
    return 1


if __name__ == "__main__":
    sys.exit(main())

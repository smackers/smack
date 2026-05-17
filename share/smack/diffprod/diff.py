from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any


@dataclass(frozen=True)
class DiffHunk:
    hunk_id: str
    old_path: str | None
    new_path: str | None
    old_start: int
    old_len: int
    new_start: int
    new_len: int
    added: tuple[str, ...] = ()
    removed: tuple[str, ...] = ()

    def to_json(self) -> dict[str, Any]:
        return {
            "hunk_id": self.hunk_id,
            "old_path": self.old_path,
            "new_path": self.new_path,
            "old_start": self.old_start,
            "old_len": self.old_len,
            "new_start": self.new_start,
            "new_len": self.new_len,
            "added": list(self.added),
            "removed": list(self.removed),
        }


_HUNK_RE = re.compile(r"^@@\s+-(?P<oa>\d+)(?:,(?P<ob>\d+))?\s+\+(?P<na>\d+)(?:,(?P<nb>\d+))?\s+@@")


def parse_unified_diff(text: str) -> list[DiffHunk]:
    """Parse git-style unified diff hunks into source line regions."""

    lines = text.splitlines()
    old_path: str | None = None
    new_path: str | None = None
    hunks: list[DiffHunk] = []
    i = 0
    while i < len(lines):
        line = lines[i]
        if line.startswith("--- "):
            old_path = clean_diff_path(line[4:].strip())
            i += 1
            continue
        if line.startswith("+++ "):
            new_path = clean_diff_path(line[4:].strip())
            i += 1
            continue

        match = _HUNK_RE.match(line)
        if not match:
            i += 1
            continue

        old_start = int(match.group("oa"))
        old_len = int(match.group("ob") or "1")
        new_start = int(match.group("na"))
        new_len = int(match.group("nb") or "1")
        i += 1

        added: list[str] = []
        removed: list[str] = []
        while i < len(lines) and not lines[i].startswith("@@"):
            body_line = lines[i]
            if body_line.startswith("--- ") or body_line.startswith("+++ "):
                break
            if body_line.startswith("+"):
                added.append(body_line[1:])
            elif body_line.startswith("-"):
                removed.append(body_line[1:])
            i += 1

        # Whitespace-only hunks still carry provenance value, but identical
        # stripped hunks are not useful for an impact seed.
        if [s.strip() for s in added] == [s.strip() for s in removed]:
            continue

        hunks.append(
            DiffHunk(
                hunk_id=f"hunk:{len(hunks) + 1}",
                old_path=old_path,
                new_path=new_path,
                old_start=old_start,
                old_len=old_len,
                new_start=new_start,
                new_len=new_len,
                added=tuple(added),
                removed=tuple(removed),
            )
        )
    return hunks


def clean_diff_path(path: str) -> str | None:
    if path == "/dev/null":
        return None
    path = path.split("\t", 1)[0]
    if path.startswith("a/") or path.startswith("b/"):
        return path[2:]
    return path


def span_intersects_hunk(
    *,
    source_file: str,
    start_line: int,
    end_line: int,
    hunk: DiffHunk,
    side: str,
) -> bool:
    path = hunk.old_path if side == "left" else hunk.new_path
    hunk_start = hunk.old_start if side == "left" else hunk.new_start
    hunk_len = hunk.old_len if side == "left" else hunk.new_len
    if path is not None and source_file and not path_matches(source_file, path):
        return False
    return line_ranges_intersect(start_line, end_line, hunk_start, hunk_len)


def line_ranges_intersect(start_line: int, end_line: int, hunk_start: int, hunk_len: int) -> bool:
    hunk_end = hunk_start if hunk_len == 0 else hunk_start + hunk_len - 1
    return start_line <= hunk_end and hunk_start <= end_line


def path_matches(source_path: str, diff_path: str) -> bool:
    source_norm = source_path.replace("\\", "/").lstrip("./")
    diff_norm = diff_path.replace("\\", "/").lstrip("./")
    return (
        source_norm == diff_norm
        or source_norm.endswith("/" + diff_norm)
        or diff_norm.endswith("/" + source_norm)
        or Path(source_norm).name == Path(diff_norm).name
    )

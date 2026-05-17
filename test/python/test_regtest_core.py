"""Tests for the pure-logic helpers in test/regtest_core.py.

Phase 4.1 pulled these out of the 452-LOC regtest.py CLI. Coverage
here pins the contract so the next refactor (regtest_core → pytest
fixtures) doesn't silently drift behaviour."""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

# regtest_core is in test/, not on sys.path by default.
_REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(_REPO_ROOT / "test"))

import regtest_core as rc  # noqa: E402


# ---------- get_result ----------


@pytest.mark.parametrize(
    "output,expected",
    [
        ("...\nSMACK timed out after 120s\n", "timeout"),
        ("...SMACK found no errors after k=2\n", "verified"),
        ("SMACK found an error.\nfile.c:42: assert false\n", "error"),
        ("garbage output", "unknown"),
        ("", "unknown"),
    ],
)
def test_get_result_classifies(output, expected):
    assert rc.get_result(output) == expected


def test_get_result_timeout_wins_over_unknown():
    # If both appear, timeout's regex order takes precedence per the
    # implementation. Pin this.
    out = "SMACK found no errors\nSMACK timed out\n"
    # Implementation checks `timeout` first.
    assert rc.get_result(out) == "timeout"


# ---------- merge ----------


def test_merge_override_replaces_existing():
    target = {"verifiers": ["boogie"], "memory": ["no-reuse"]}
    rc.merge(target, {"verifiers": ["corral"]})
    assert target["verifiers"] == ["corral"]
    assert target["memory"] == ["no-reuse"]  # untouched


def test_merge_append_extends_existing():
    target = {"flags": ["--foo"]}
    rc.merge(target, {"flags": ["--bar"]})
    assert target["flags"] == ["--foo", "--bar"]


def test_merge_append_seeds_when_absent():
    target = {}
    rc.merge(target, {"checkbpl": ["grep PASS"]})
    assert target["checkbpl"] == ["grep PASS"]


def test_merge_unknown_keys_ignored():
    target = {}
    rc.merge(target, {"not-a-field": "ignored"})
    assert "not-a-field" not in target


# ---------- get_extensions ----------


@pytest.mark.parametrize(
    "spec,expected_subset",
    [
        ("c", {"*.c"}),
        ("cplusplus", {"*.cc", "*.cpp"}),
        ("rust", {"*.rs"}),
        ("llvm-ir", {"*.ll"}),
        ("cargo", {"Cargo.toml"}),
    ],
)
def test_get_extensions_single_language(spec, expected_subset):
    assert rc.get_extensions(spec) == expected_subset


def test_get_extensions_multi_language_union():
    assert rc.get_extensions("c,rust") == {"*.c", "*.rs"}


def test_get_extensions_unknown_language_raises():
    with pytest.raises(KeyError) as exc:
        rc.get_extensions("klingon")
    assert "klingon" in str(exc.value)


def test_get_extensions_partial_unknown_raises():
    with pytest.raises(KeyError):
        rc.get_extensions("c,klingon")


# ---------- load_metadata ----------


def _stub_loader(file_obj):
    """yaml.safe_load stand-in: parses ``key: value\\nkey: value`` lines
    into a dict — keeps these tests independent of PyYAML availability."""
    out = {}
    for line in file_obj:
        line = line.rstrip()
        if not line or line.startswith("#"):
            continue
        if ":" in line:
            k, _, v = line.partition(":")
            v = v.strip()
            # Crude list literal parser for ``[a, b]`` / ``["a", "b"]``.
            if v.startswith("[") and v.endswith("]"):
                inner = v[1:-1]
                items = [s.strip().strip("\"'") for s in inner.split(",") if s.strip()]
                out[k.strip()] = items
            elif v in ("true", "True"):
                out[k.strip()] = True
            elif v in ("false", "False"):
                out[k.strip()] = False
            elif v.isdigit():
                out[k.strip()] = int(v)
            else:
                out[k.strip()] = v.strip("\"'")
    return out


def test_load_metadata_directives_picked_up(tmp_path):
    test_file = tmp_path / "demo.c"
    test_file.write_text(
        "// @flag --unroll=4\n"
        "// @expect verified\n"
        "// @checkbpl grep PASS\n"
        "int main() { return 0; }\n"
    )
    m = rc.load_metadata(str(test_file), test_root=str(tmp_path), yaml_loader=_stub_loader)
    assert m["expect"] == "verified"
    assert "--unroll=4" in m["flags"]
    assert "grep PASS" in m["checkbpl"]
    assert m["skip"] is False


def test_load_metadata_skip_directive(tmp_path):
    test_file = tmp_path / "skipped.c"
    test_file.write_text("// @skip\n// @expect verified\n")
    m = rc.load_metadata(str(test_file), test_root=str(tmp_path), yaml_loader=_stub_loader)
    assert m["skip"] is True


def test_load_metadata_layered_yaml_overrides(tmp_path):
    sub = tmp_path / "sub"
    sub.mkdir()
    (tmp_path / "config.yml").write_text("time-limit: 60\nflags: [--root-flag]\n")
    (sub / "config.yml").write_text("time-limit: 120\nflags: [--sub-flag]\n")
    test_file = sub / "demo.c"
    test_file.write_text("// @expect verified\n")
    m = rc.load_metadata(str(test_file), test_root=str(tmp_path), yaml_loader=_stub_loader)
    # OVERRIDE: deeper config's time-limit wins.
    assert m["time-limit"] == 120
    # APPEND: flags accumulate root → sub.
    assert m["flags"] == ["--root-flag", "--sub-flag"]


def test_load_metadata_missing_expect_defaults_to_verified(tmp_path):
    test_file = tmp_path / "demo.c"
    test_file.write_text("int main() { return 0; }\n")
    m = rc.load_metadata(str(test_file), test_root=str(tmp_path), yaml_loader=_stub_loader)
    assert m["expect"] == "verified"


# ---------- get_tests ----------


def test_get_tests_globs_extensions(tmp_path):
    folder = tmp_path / "basic"
    folder.mkdir()
    (folder / "a.c").write_text("")
    (folder / "b.c").write_text("")
    (folder / "skip.txt").write_text("")
    tests = rc.get_tests("basic", {"*.c"}, test_root=str(tmp_path))
    assert {Path(t).name for t in tests} == {"a.c", "b.c"}


def test_get_tests_excludes_rust_in_cargo_workspace(tmp_path):
    cargo_dir = tmp_path / "rust" / "myproj"
    cargo_dir.mkdir(parents=True)
    (cargo_dir / "Cargo.toml").write_text("")
    (cargo_dir / "main.rs").write_text("")
    standalone = tmp_path / "rust" / "standalone.rs"
    standalone.write_text("")
    tests = rc.get_tests("rust", {"*.rs"}, test_root=str(tmp_path))
    names = {Path(t).name for t in tests}
    assert "standalone.rs" in names
    assert "main.rs" not in names


def test_get_tests_sorted(tmp_path):
    folder = tmp_path / "f"
    folder.mkdir()
    for n in ["zebra.c", "alpha.c", "mango.c"]:
        (folder / n).write_text("")
    tests = rc.get_tests("f", {"*.c"}, test_root=str(tmp_path))
    assert [Path(t).name for t in tests] == ["alpha.c", "mango.c", "zebra.c"]


# ---------- module surface ----------


def test_public_api_in_dunder_all():
    assert set(rc.__all__) >= {
        "get_result",
        "merge",
        "load_metadata",
        "get_extensions",
        "get_tests",
        "LANGUAGES",
        "OVERRIDE_FIELDS",
        "APPEND_FIELDS",
        "TEST_ROOT",
    }

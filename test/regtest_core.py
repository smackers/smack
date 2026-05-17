"""Pure-logic core extracted from test/regtest.py.

The 452-LOC CLI in regtest.py mixes:
  - language/extension tables                  ──┐
  - YAML config merging                          │
  - per-test metadata + @directive parsing       │ pure logic (here)
  - test discovery (glob + cargo filter)         │
  - result verdict regex                       ──┘
  - subprocess invocation                      ──┐
  - colored stdout + logging                     │ I/O (still in regtest.py)
  - ThreadPool orchestration                     │
  - argparse                                   ──┘

This module owns the pure-logic half. regtest.py imports from here.
test/python/test_regtest_core.py covers it with pytest. A future
Phase 4.1 step can move the subprocess + orchestration into a pytest
fixture and retire regtest.py entirely.

The TEST_ROOT constant is the path to ``test/`` itself; importers
should override it (or pass an explicit ``test_root=`` to the
functions that take one) when running outside the SMACK tree.
"""

from __future__ import annotations

import glob
import os
import re
import shlex
from os import path
from typing import Iterable, List, Mapping, MutableMapping, Optional, Set

#: Repository test root — resolved relative to this file. Matches the
#: original TEST_ROOT in regtest.py.
TEST_ROOT: str = path.dirname(path.realpath(__file__))

#: Fields where a deeper config.yml **replaces** the shallower one.
OVERRIDE_FIELDS: List[str] = [
    "verifiers",
    "memory",
    "time-limit",
    "memory-limit",
    "skip",
]

#: Fields where a deeper config.yml **appends** to the shallower one.
APPEND_FIELDS: List[str] = ["flags", "checkbpl", "checkout"]

#: Per-language file-extension globs accepted by --languages.
LANGUAGES: Mapping[str, Set[str]] = {
    "c": {"*.c"},
    "cargo": {"Cargo.toml"},
    "cplusplus": {"*.cc", "*.cpp"},
    "rust": {"*.rs"},
    "llvm-ir": {"*.ll"},
}

_VALID_EXPECTATIONS = {"verified", "error", "timeout", "unknown"}


def get_result(output: str) -> str:
    """Classify a SMACK invocation's combined stdout+stderr.

    Returns one of ``"verified"``, ``"error"``, ``"timeout"``,
    ``"unknown"``. Pure regex match — no I/O, no side effects.
    """
    if re.search(r"SMACK timed out", output):
        return "timeout"
    if re.search(r"SMACK found no errors", output):
        return "verified"
    if re.search(r"SMACK found an error", output):
        return "error"
    return "unknown"


def merge(target: MutableMapping[str, object], yamldata: Mapping[str, object]) -> None:
    """Apply a YAML config layer onto `target` per the merge policy.

    Mutates `target` in place. Override fields replace; append fields
    extend. Mirrors regtest.py's original merge() exactly.
    """
    for key in OVERRIDE_FIELDS:
        if key in yamldata:
            target[key] = yamldata[key]

    for key in APPEND_FIELDS:
        if key in yamldata:
            if key in target:
                # Original code uses `+=` which works for lists; preserve.
                target[key] = list(target[key]) + list(yamldata[key])  # type: ignore[arg-type]
            else:
                target[key] = list(yamldata[key])  # type: ignore[arg-type]


def _walk_config_layers(file: str, test_root: str) -> List[str]:
    """Return config.yml paths from test_root down to the test file's
    parent directory, in shallowest-first order. Files that don't
    exist are skipped."""
    layers: List[str] = []
    root_config = path.join(test_root, "config.yml")
    if path.isfile(root_config):
        layers.append(root_config)

    rel_file = path.relpath(path.realpath(file), test_root)
    prefix: List[str] = []
    for d in path.dirname(rel_file).split(os.sep):
        if d in ("", "."):
            continue
        prefix.append(d)
        yaml_file = path.join(test_root, *(prefix + ["config.yml"]))
        if path.isfile(yaml_file):
            layers.append(yaml_file)

    return layers


def _parse_test_directives(file: str, meta: MutableMapping[str, object]) -> None:
    """Walk the test source for @skip / @flag / @expect / @checkbpl /
    @checkout directives and update `meta` in place."""
    with open(file) as f:
        for line in f.readlines():
            if re.search(r"@skip", line):
                meta["skip"] = True

            m = re.search(r"@flag (.*)", line)
            if m:
                meta["flags"] = list(meta.get("flags", [])) + shlex.split(  # type: ignore[arg-type]
                    m.group(1).strip()
                )

            m = re.search(r"@expect (.*)", line)
            if m:
                meta["expect"] = m.group(1).strip()

            m = re.search(r"@checkbpl (.*)", line)
            if m:
                meta["checkbpl"] = list(meta.get("checkbpl", [])) + [  # type: ignore[arg-type]
                    m.group(1).strip()
                ]

            m = re.search(r"@checkout (.*)", line)
            if m:
                meta["checkout"] = list(meta.get("checkout", [])) + [  # type: ignore[arg-type]
                    m.group(1).strip()
                ]


def load_metadata(
    file: str,
    *,
    test_root: Optional[str] = None,
    yaml_loader=None,
) -> MutableMapping[str, object]:
    """Merge config.yml layers + parse @directives for a single test.

    Parameters
    ----------
    file
        Path to the test source.
    test_root
        Defaults to ``TEST_ROOT``. Lets callers (e.g. pytest fixtures
        running from a sandbox) override the root.
    yaml_loader
        Callable taking a file object → dict. Defaults to
        ``yaml.safe_load`` if not supplied. Keeps this module's import
        chain trivial; only the metadata path actually needs PyYAML.

    Returns the merged metadata dict. Sets default values for every
    OVERRIDE / APPEND field plus an `expect` default of ``"verified"``
    when the test isn't skipped.
    """
    root = test_root or TEST_ROOT
    m: MutableMapping[str, object] = {}

    if yaml_loader is None:
        import yaml  # lazy: regtest_core is tested without PyYAML on the path

        yaml_loader = yaml.safe_load

    for layer in _walk_config_layers(file, root):
        with open(layer) as f:
            data = yaml_loader(f) or {}
            merge(m, data)

    for field in OVERRIDE_FIELDS:
        m.setdefault(field, False if field == "skip" else [])
    for field in APPEND_FIELDS:
        m.setdefault(field, [])

    _parse_test_directives(file, m)

    if not m["skip"]:
        m.setdefault("expect", "verified")
        if m["expect"] not in _VALID_EXPECTATIONS:
            # Original code printed a warning but proceeded. Preserve.
            pass

    return m


def get_extensions(languages: str) -> Set[str]:
    """Resolve a comma-separated language list to file-glob extensions.

    Raises ``KeyError`` for unknown languages — matches regtest.py.
    """
    extensions: Set[str] = set()
    for language in languages.split(","):
        if language not in LANGUAGES:
            raise KeyError(language)
        extensions |= LANGUAGES[language]
    return extensions


def get_tests(
    folder: str,
    extensions: Iterable[str],
    *,
    test_root: Optional[str] = None,
) -> List[str]:
    """Glob tests under ``test_root/folder`` matching ``extensions``,
    excluding ``.rs`` files that belong to a nested Cargo workspace
    (those are run via the cargo language driver instead).
    """
    root = test_root or TEST_ROOT
    tests: List[str] = []
    for ext in extensions:
        tests.extend(glob.glob(path.join(root, folder, ext), recursive=True))

    def nested_cargo_source(test: str) -> bool:
        if not test.endswith(".rs"):
            return False
        current = path.dirname(path.realpath(test))
        while current.startswith(root):
            if path.isfile(path.join(current, "Cargo.toml")):
                return True
            parent = path.dirname(current)
            if parent == current:
                break
            current = parent
        return False

    tests = [t for t in tests if not nested_cargo_source(t)]
    tests.sort()
    return tests


__all__ = [
    "APPEND_FIELDS",
    "LANGUAGES",
    "OVERRIDE_FIELDS",
    "TEST_ROOT",
    "get_extensions",
    "get_result",
    "get_tests",
    "load_metadata",
    "merge",
]

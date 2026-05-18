"""Smoke tests for the share/smack/__init__.py public surface."""

from __future__ import annotations

import re

import smack


def test_version_is_semver_string():
    assert isinstance(smack.__version__, str)
    assert re.fullmatch(
        r"\d+\.\d+\.\d+(?:[.\-+].*)?", smack.__version__
    ), f"__version__={smack.__version__!r} is not semver-shaped"


def test_version_matches_constants_module():
    from smack import constants

    assert smack.__version__ == constants.VERSION


def test_public_api_is_advertised_in_all():
    assert set(smack.__all__) == {"__version__", "VResult", "VProperty", "main"}


def test_vresult_and_vproperty_are_re_exported():
    from smack.cli.results import VProperty as SrcVProperty
    from smack.cli.results import VResult as SrcVResult

    assert smack.VResult is SrcVResult
    assert smack.VProperty is SrcVProperty


def test_main_is_callable():
    # Don't actually invoke (it would call arguments() and exit). Just
    # confirm the attribute is a callable.
    assert callable(smack.main)

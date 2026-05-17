import contextlib

import pytest


def pytest_addoption(parser):
    with contextlib.suppress(ValueError):
        parser.addoption(
            "--runslow",
            action="store_true",
            default=False,
            help="run tests marked slow",
        )


def pytest_configure(config):
    config.addinivalue_line("markers", "slow: opt-in slow integration/stress tests")


def pytest_collection_modifyitems(config, items):
    for item in items:
        if item.module.__name__.endswith("test_diffprod_pipeline") and item.name.startswith(
            "test_smack_"
        ):
            item.add_marker(pytest.mark.slow)

    markexpr = getattr(config.option, "markexpr", "") or ""
    if config.getoption("--runslow") or "slow" in markexpr:
        return
    skip_slow = pytest.mark.skip(reason="slow test; run with --runslow or -m slow")
    for item in items:
        if "slow" in item.keywords:
            item.add_marker(skip_slow)

import importlib.util
import sys

import pytest
from smack_test_paths import REPO_ROOT


def load_builder_module():
    module_path = REPO_ROOT / "tools" / "build_bearssl_bitcode.py"
    spec = importlib.util.spec_from_file_location("build_bearssl_bitcode", module_path)
    assert spec is not None
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def test_default_driver_exposes_expected_entry():
    builder = load_builder_module()

    source = builder.default_driver_source()

    assert "bearssl_devirt_entry" in source
    assert "bearssl_devirt_hash_entry" in source
    assert "bearssl_devirt_block_entry" in source
    assert "br_ssl_client_init_full" in source
    assert "hash->update" in source
    assert "cbc_impl->run" in source


def test_collect_bearssl_sources_requires_checkout_shape(tmp_path):
    builder = load_builder_module()

    with pytest.raises(builder.BuildError, match="not a BearSSL source checkout"):
        builder.collect_bearssl_sources(tmp_path)


def test_collect_bearssl_sources_finds_src_files(tmp_path):
    builder = load_builder_module()
    (tmp_path / "inc").mkdir()
    (tmp_path / "inc" / "bearssl.h").write_text("")
    (tmp_path / "src").mkdir()
    source = tmp_path / "src" / "hash.c"
    source.write_text("int f(void) { return 0; }")

    assert builder.collect_bearssl_sources(tmp_path) == [source]

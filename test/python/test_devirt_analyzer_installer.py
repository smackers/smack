import importlib.util
import sys

from smack_test_paths import REPO_ROOT


def load_installer_module():
    module_path = REPO_ROOT / "tools" / "install_devirt_analyzers.py"
    spec = importlib.util.spec_from_file_location("install_devirt_analyzers", module_path)
    assert spec is not None
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def test_discover_tool_finds_local_binary(tmp_path):
    installer = load_installer_module()
    tool = tmp_path / "bin" / "wpa"
    tool.parent.mkdir()
    tool.write_text("#!/bin/sh\n")

    found = installer.discover_tool(["wpa"], [tmp_path])

    assert found["wpa"] == str(tool.resolve())


def test_discover_tool_finds_svf_devirt_oracle(tmp_path):
    installer = load_installer_module()
    tool = tmp_path / "bin" / "svf-devirt-oracle"
    tool.parent.mkdir()
    tool.write_text("#!/bin/sh\n")

    found = installer.discover_tool(["svf-devirt-oracle"], [tmp_path])

    assert found["svf-devirt-oracle"] == str(tool.resolve())


def test_ensure_svf_devirt_oracle_reports_missing_build_dirs(tmp_path):
    installer = load_installer_module()
    record = {"status": "available", "tools": {"wpa": "/bin/wpa"}}

    updated = installer.ensure_svf_devirt_oracle(
        record,
        install_root=tmp_path,
        llvm={"llvm_config": "/missing", "bindir": "/missing", "version": "14.0.0"},
        timeout=1,
    )

    assert updated["status"] == "available"
    assert "svf_devirt_oracle_error" in updated


def test_command_record_serializes_paths():
    installer = load_installer_module()
    result = installer.CommandResult(
        command=["true"],
        cwd=REPO_ROOT,
        returncode=0,
        wall_ms=1.0,
        output_tail="",
    )

    record = installer.command_record(result)

    assert record["cwd"] == str(REPO_ROOT)
    assert record["command"] == ["true"]


def test_patch_phasar_compat_rewrites_lifetimebound_macro(tmp_path):
    installer = load_installer_module()
    macros = tmp_path / "include" / "phasar" / "Utils" / "Macros.h"
    macros.parent.mkdir(parents=True)
    macros.write_text("#elif __has_cpp_attribute([[lifetimebound]])\n")

    assert installer.patch_phasar_compat(tmp_path) is True

    assert "__has_cpp_attribute(lifetimebound)" in macros.read_text()

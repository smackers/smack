import os
import shutil
import subprocess
from pathlib import Path
from typing import Any

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
BOOGIE_PARSER_ROOT = REPO_ROOT.parent
SHARE_DIR = REPO_ROOT / "share"


def _existing(candidates):
    for candidate in candidates:
        if candidate is None:
            continue
        path = Path(candidate)
        if path.exists():
            return path
    return None


def tool_path(name: str):
    build_dirs = []
    if os.environ.get("SMACK_BUILD_DIR"):
        build_dirs.append(Path(os.environ["SMACK_BUILD_DIR"]))
    build_dirs.extend(
        [
            REPO_ROOT / "build-llvm22c",
            REPO_ROOT / "build-newpm",
            REPO_ROOT / "build",
        ]
    )
    path = _existing([build_dir / name for build_dir in build_dirs] + [shutil.which(name)])
    if path is None:
        pytest.skip(f"{name} not found")
    return str(path)


def clang_path():
    path = _existing(
        [
            "/usr/lib/llvm-22/bin/clang-22",
            shutil.which("clang-22"),
            shutil.which("clang"),
        ]
    )
    if path is None:
        pytest.skip("clang not found")
    return str(path)


def clangxx_path():
    path = _existing(
        [
            "/usr/lib/llvm-22/bin/clang++-22",
            shutil.which("clang++-22"),
            shutil.which("clang++"),
        ]
    )
    if path is None:
        pytest.skip("clang++ not found")
    return str(path)


def llvm_link_path():
    path = _existing(
        [
            "/usr/lib/llvm-22/bin/llvm-link-22",
            shutil.which("llvm-link-22"),
            shutil.which("llvm-link"),
        ]
    )
    if path is None:
        pytest.skip("llvm-link not found")
    return str(path)


def svf_wpa_path():
    return _existing(
        [
            os.environ.get("SMACK_SVF_WPA"),
            REPO_ROOT / "external" / "SVF" / "build-llvm22" / "bin" / "wpa",
            BOOGIE_PARSER_ROOT / "SVF" / "build-llvm22" / "bin" / "wpa",
            "/tmp/smack-external-tools/SVF/build-llvm22/bin/wpa",
            shutil.which("wpa"),
        ]
    )


def svf_extapi_path():
    return _existing(
        [
            os.environ.get("SMACK_SVF_EXTAPI"),
            REPO_ROOT / "external" / "SVF" / "build-llvm22" / "lib" / "extapi.bc",
            BOOGIE_PARSER_ROOT / "SVF" / "build-llvm22" / "lib" / "extapi.bc",
            "/tmp/smack-external-tools/SVF/build-llvm22/lib/extapi.bc",
        ]
    )


def diff_product_cli():
    candidates = [
        REPO_ROOT / "bin" / "smack",
        shutil.which("smack"),
        "/usr/local/bin/smack",
    ]
    checked = []
    for smack in candidates:
        path = _existing([smack])
        if path is None:
            continue
        completed = subprocess.run(
            [str(path), "--help"],
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            check=False,
            timeout=timeout_seconds("SMACK_HELP", 30),
        )
        checked.append((str(path), completed.stdout))
        if completed.returncode == 0 and "--diff-product" in completed.stdout:
            return str(path)
    if checked:
        pytest.fail("available smack executable does not expose --diff-product")
    pytest.skip("smack executable not found")


def deltarel_roots():
    roots = []
    if os.environ.get("SMACK_DELTAREL_ROOT"):
        roots.append(Path(os.environ["SMACK_DELTAREL_ROOT"]))
    roots.extend(
        [
            REPO_ROOT / "external" / "deltarel",
            BOOGIE_PARSER_ROOT / "deltarel",
        ]
    )
    return [root for root in roots if (root / "deltarel" / "product_v2.py").exists()]


def pythonpath_env(extra_paths=()):
    paths = [str(SHARE_DIR), *(str(path) for path in deltarel_roots()), *map(str, extra_paths)]
    if os.environ.get("PYTHONPATH"):
        paths.append(os.environ["PYTHONPATH"])
    env = dict(os.environ)
    env["PYTHONPATH"] = os.pathsep.join(paths)
    return env


def tool_path_env(extra_paths=()):
    build_dirs = []
    if os.environ.get("SMACK_BUILD_DIR"):
        build_dirs.append(Path(os.environ["SMACK_BUILD_DIR"]))
    build_dirs.extend(
        [
            REPO_ROOT / "build-llvm22c",
            REPO_ROOT / "build-newpm",
            REPO_ROOT / "build",
        ]
    )
    paths = [
        *(str(path) for path in extra_paths),
        *(str(path) for path in build_dirs if path.exists()),
        "/usr/lib/llvm-22/bin",
    ]
    if os.environ.get("PATH"):
        paths.append(os.environ["PATH"])
    env = pythonpath_env()
    env["PATH"] = os.pathsep.join(paths)
    svf_wpa = svf_wpa_path()
    svf_extapi = svf_extapi_path()
    if svf_wpa is not None and svf_extapi is not None:
        env.setdefault("SMACK_SVF_WPA", str(svf_wpa))
        env.setdefault("SMACK_SVF_EXTAPI", str(svf_extapi))
    return env


def timeout_seconds(name: str, default: int) -> int:
    for env_name in (f"SMACK_TEST_{name}_TIMEOUT", "SMACK_TEST_TIMEOUT"):
        value = os.environ.get(env_name)
        if value:
            return int(value)
    return default


def run_with_timeout(
    args,
    *,
    timeout_name: str = "SUBPROCESS",
    default_timeout: int = 120,
    **kwargs: Any,
):
    timeout = timeout_seconds(timeout_name, default_timeout)
    try:
        return subprocess.run(args, timeout=timeout, **kwargs)
    except subprocess.TimeoutExpired as exc:
        output = exc.stdout or exc.stderr or ""
        if isinstance(output, bytes):
            output = output.decode(errors="replace")
        tail = output[-4000:] if output else ""
        command = " ".join(str(arg) for arg in args)
        pytest.fail(f"command timed out after {timeout}s: {command}\n{tail}")

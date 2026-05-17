#!/usr/bin/env python3
"""Install optional devirtualization analyzers into a local build directory.

The installer is intentionally best-effort: it records each analyzer as
``available`` or ``failed`` in a manifest so comparison runs can use the tools
that are present and report the rest explicitly.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shlex
import shutil
import subprocess
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any


SVF_URL = "https://github.com/SVF-tools/SVF.git"
PHASAR_URL = "https://github.com/secure-software-engineering/phasar.git"


class InstallError(RuntimeError):
    """Raised when an analyzer install step fails."""


@dataclass(frozen=True)
class CommandResult:
    command: list[str]
    cwd: Path
    returncode: int
    wall_ms: float
    output_tail: str


def _repo_root() -> Path:
    return Path(__file__).resolve().parents[1]


def _tail(text: str, *, limit: int = 50) -> str:
    return "\n".join(text.splitlines()[-limit:])


def run_command(
    args: list[str],
    *,
    cwd: Path,
    timeout: int,
    env: dict[str, str] | None = None,
    check: bool = True,
) -> CommandResult:
    start = time.monotonic()
    try:
        completed = subprocess.run(
            args,
            cwd=cwd,
            env=env,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            timeout=timeout,
            check=False,
        )
    except subprocess.TimeoutExpired as exc:
        output = exc.stdout or ""
        if isinstance(output, bytes):
            output = output.decode(errors="replace")
        completed = subprocess.CompletedProcess(args, 124, output)
    wall_ms = (time.monotonic() - start) * 1000.0
    result = CommandResult(
        command=args,
        cwd=cwd,
        returncode=completed.returncode,
        wall_ms=wall_ms,
        output_tail=_tail(completed.stdout or ""),
    )
    if check and result.returncode != 0:
        raise InstallError(
            "command failed with exit code "
            f"{result.returncode}: {' '.join(args)}\n{result.output_tail}"
        )
    return result


def command_record(result: CommandResult) -> dict[str, Any]:
    return {
        "command": result.command,
        "cwd": str(result.cwd),
        "returncode": result.returncode,
        "wall_ms": result.wall_ms,
        "output_tail": result.output_tail,
    }


def resolve_program(value: str | None, name: str) -> Path:
    if value:
        path = Path(value)
        if path.exists():
            return path.resolve()
        raise InstallError(f"required program not found: {value}")
    found = shutil.which(name)
    if found:
        return Path(found).resolve()
    raise InstallError(f"required program not found: {name}")


def llvm_info(llvm_config: Path, *, timeout: int) -> dict[str, Any]:
    version = run_command([str(llvm_config), "--version"], cwd=Path.cwd(), timeout=timeout)
    cmake_dir = run_command(
        [str(llvm_config), "--cmakedir"], cwd=Path.cwd(), timeout=timeout
    )
    bindir = run_command([str(llvm_config), "--bindir"], cwd=Path.cwd(), timeout=timeout)
    return {
        "llvm_config": str(llvm_config),
        "version": version.output_tail.strip(),
        "cmake_dir": cmake_dir.output_tail.strip(),
        "bindir": bindir.output_tail.strip(),
    }


def llvm_tag(llvm: dict[str, Any]) -> str:
    version = str(llvm.get("version", "unknown"))
    return "llvm" + re.sub(r"[^A-Za-z0-9_.-]+", "-", version)


def phasar_llvm_version(llvm: dict[str, Any]) -> str:
    version = str(llvm.get("version", ""))
    pieces = version.split(".")
    if len(pieces) >= 2:
        return ".".join(pieces[:2])
    return pieces[0] if pieces and pieces[0] else version


def cmake_info(cmake: Path, *, timeout: int) -> dict[str, str]:
    version = run_command([str(cmake), "--version"], cwd=Path.cwd(), timeout=timeout)
    first_line = version.output_tail.splitlines()[0] if version.output_tail else ""
    return {"cmake": str(cmake), "version": first_line}


def git_clone_or_fetch(
    *,
    url: str,
    source_dir: Path,
    ref: str,
    timeout: int,
    recursive: bool = False,
) -> list[CommandResult]:
    source_dir.parent.mkdir(parents=True, exist_ok=True)
    commands: list[CommandResult] = []
    if (source_dir / ".git").is_dir():
        commands.append(
            run_command(["git", "-C", str(source_dir), "fetch", "--tags"], cwd=Path.cwd(), timeout=timeout)
        )
    else:
        clone_args = ["git", "clone"]
        if recursive:
            clone_args.append("--recursive")
        clone_args.extend([url, str(source_dir)])
        commands.append(run_command(clone_args, cwd=Path.cwd(), timeout=timeout))

    commands.append(
        run_command(["git", "-C", str(source_dir), "checkout", ref], cwd=Path.cwd(), timeout=timeout)
    )
    commands.append(
        run_command(
            ["git", "-C", str(source_dir), "submodule", "update", "--init", "--recursive"],
            cwd=Path.cwd(),
            timeout=timeout,
            check=False,
        )
    )
    return commands


def git_commit(source_dir: Path, *, timeout: int) -> str | None:
    if not (source_dir / ".git").is_dir():
        return None
    result = run_command(
        ["git", "-C", str(source_dir), "rev-parse", "HEAD"],
        cwd=Path.cwd(),
        timeout=timeout,
        check=False,
    )
    if result.returncode != 0:
        return None
    return result.output_tail.strip()


def patch_phasar_compat(source_dir: Path) -> bool:
    macros = source_dir / "include" / "phasar" / "Utils" / "Macros.h"
    if not macros.exists():
        return False
    text = macros.read_text()
    fixed = text.replace(
        "__has_cpp_attribute([[lifetimebound]])",
        "__has_cpp_attribute(lifetimebound)",
    )
    if fixed == text:
        return False
    macros.write_text(fixed)
    return True


def discover_tool(names: list[str], roots: list[Path]) -> dict[str, str]:
    found: dict[str, str] = {}
    for name in names:
        for root in roots:
            if not root.exists():
                continue
            for path in root.rglob(name):
                if path.is_file():
                    found[name] = str(path.resolve())
                    break
            if name in found:
                break
        if name not in found:
            system_path = shutil.which(name)
            if system_path:
                found[name] = str(Path(system_path).resolve())
    return found


def llvm_tools(info: dict[str, Any]) -> dict[str, str]:
    bindir = Path(str(info.get("bindir", "")))
    tools: dict[str, str] = {}
    for name in ("clang", "llvm-link", "llvm-dis", "llvm-as", "opt"):
        path = bindir / name
        if path.exists():
            tools[name] = str(path.resolve())
    return tools


def _llvm_config_tokens(llvm: dict[str, Any], option: str, *, timeout: int) -> list[str]:
    llvm_config = Path(str(llvm.get("llvm_config", "")))
    if not llvm_config.exists():
        raise InstallError(f"required llvm-config not found for SVF sidecar: {llvm_config}")
    result = run_command([str(llvm_config), option], cwd=Path.cwd(), timeout=timeout)
    return shlex.split(result.output_tail.strip())


def cmake_env(llvm: dict[str, Any]) -> dict[str, str]:
    env = os.environ.copy()
    bindir = str(llvm.get("bindir", ""))
    env["PATH"] = f"{bindir}{os.pathsep}{env.get('PATH', '')}" if bindir else env.get("PATH", "")
    return env


def build_svf_devirt_oracle(
    *,
    install_root: Path,
    llvm: dict[str, Any],
    source_dir: Path,
    build_dir: Path,
    install_dir: Path,
    timeout: int,
) -> tuple[dict[str, str], list[CommandResult]]:
    tag = llvm_tag(llvm)
    oracle_build_dir = install_root / "svf-local" / f"build-{tag}"
    oracle_build_dir.mkdir(parents=True, exist_ok=True)
    oracle_path = oracle_build_dir / "svf-devirt-oracle"
    source = _repo_root() / "tools" / "svf_devirt_oracle.cpp"
    if not source.exists():
        raise InstallError(f"SVF local devirt sidecar source not found: {source}")

    bindir = Path(str(llvm.get("bindir", "")))
    compiler = bindir / "clang++"
    if not compiler.exists():
        compiler = resolve_program(None, "c++")

    extapi = install_dir / "lib" / "extapi.bc"
    core_lib = install_dir / "lib" / "libSvfCore.a"
    llvm_lib = install_dir / "lib" / "libSvfLLVM.a"
    for required in (core_lib, llvm_lib):
        if not required.exists():
            raise InstallError(f"required SVF library not found for sidecar: {required}")

    cxxflags = _llvm_config_tokens(llvm, "--cxxflags", timeout=timeout)
    ldflags = _llvm_config_tokens(llvm, "--ldflags", timeout=timeout)
    llvm_libs = _llvm_config_tokens(llvm, "--libs", timeout=timeout)
    system_libs = _llvm_config_tokens(llvm, "--system-libs", timeout=timeout)

    include_flags = [
        f"-I{source_dir / 'svf' / 'include'}",
        f"-I{source_dir / 'svf-llvm' / 'include'}",
        f"-I{build_dir}",
        f"-I{build_dir / 'include'}",
        f"-I{build_dir / 'include' / 'SVF'}",
        f"-I{install_dir / 'include'}",
    ]
    rpath = f"{install_dir / 'lib'}:{Path(str(llvm.get('bindir', ''))).parent / 'lib'}"
    command = [
        str(compiler),
        f"-DSVF_INSTALL_EXTAPI_BC=\"{extapi}\"",
        *cxxflags,
        "-std=gnu++17",
        "-O2",
        *include_flags,
        str(source),
        "-o",
        str(oracle_path),
        str(core_lib),
        str(llvm_lib),
        *ldflags,
        *llvm_libs,
        str(core_lib),
        "-lz3",
        *system_libs,
        f"-Wl,-rpath,{rpath}",
    ]
    result = run_command(command, cwd=_repo_root(), timeout=timeout, env=cmake_env(llvm))
    tools = {
        "svf-devirt-oracle": str(oracle_path.resolve()),
        "svf-local-devirt": str(oracle_path.resolve()),
    }
    return tools, [result]


def build_svf(
    *,
    install_root: Path,
    llvm: dict[str, Any],
    cmake: Path,
    ref: str,
    jobs: int,
    timeout: int,
) -> dict[str, Any]:
    source_dir = install_root / "svf" / "src"
    tag = llvm_tag(llvm)
    build_dir = install_root / "svf" / f"build-{tag}"
    install_dir = install_root / "svf" / f"install-{tag}"
    commands: list[CommandResult] = []
    record: dict[str, Any] = {
        "url": SVF_URL,
        "ref": ref,
        "source_dir": str(source_dir),
        "build_dir": str(build_dir),
        "install_dir": str(install_dir),
        "status": "failed",
        "tools": {},
        "llvm_tools": llvm_tools(llvm),
    }

    try:
        commands.extend(
            git_clone_or_fetch(
                url=SVF_URL,
                source_dir=source_dir,
                ref=ref,
                timeout=timeout,
                recursive=True,
            )
        )
        build_dir.mkdir(parents=True, exist_ok=True)
        install_dir.mkdir(parents=True, exist_ok=True)
        cmake_args = [
            str(cmake),
            "-S",
            str(source_dir),
            "-B",
            str(build_dir),
            "-DCMAKE_BUILD_TYPE=Release",
            f"-DCMAKE_INSTALL_PREFIX={install_dir}",
            f"-DLLVM_DIR={llvm['cmake_dir']}",
            f"-DCMAKE_C_COMPILER={Path(str(llvm['bindir'])) / 'clang'}",
            f"-DCMAKE_CXX_COMPILER={Path(str(llvm['bindir'])) / 'clang++'}",
            "-DSVF_WARN_AS_ERROR=OFF",
            "-DSVF_USE_LTO=OFF",
        ]
        commands.append(
            run_command(cmake_args, cwd=install_root, timeout=timeout, env=cmake_env(llvm))
        )
        commands.append(
            run_command(
                [str(cmake), "--build", str(build_dir), "-j", str(jobs)],
                cwd=install_root,
                timeout=timeout,
                env=cmake_env(llvm),
            )
        )
        commands.append(
            run_command(
                [str(cmake), "--install", str(build_dir)],
                cwd=install_root,
                timeout=timeout,
                env=cmake_env(llvm),
                check=False,
            )
        )
        tools = discover_tool(
            ["wpa", "svf-ex", "llvm2svf", "svf-devirt-oracle"],
            [install_dir / "bin", build_dir / "bin", build_dir, source_dir],
        )
        if not any(name in tools for name in ("wpa", "svf-ex")):
            raise InstallError("SVF build finished but no wpa or svf-ex binary was found")
        try:
            oracle_tools, oracle_commands = build_svf_devirt_oracle(
                install_root=install_root,
                llvm=llvm,
                source_dir=source_dir,
                build_dir=build_dir,
                install_dir=install_dir,
                timeout=timeout,
            )
            tools.update(oracle_tools)
            commands.extend(oracle_commands)
        except InstallError as exc:
            record["svf_devirt_oracle_error"] = str(exc)
        record.update({"status": "available", "tools": tools})
    except InstallError as exc:
        record["error"] = str(exc)
        record["tools"] = discover_tool(
            ["wpa", "svf-ex", "llvm2svf", "svf-devirt-oracle"],
            [install_dir, build_dir],
        )

    record["commit"] = git_commit(source_dir, timeout=timeout)
    record["commands"] = [command_record(command) for command in commands]
    return record


def build_phasar(
    *,
    install_root: Path,
    llvm: dict[str, Any],
    cmake: Path,
    ref: str,
    jobs: int,
    timeout: int,
) -> dict[str, Any]:
    source_dir = install_root / "phasar" / "src"
    tag = llvm_tag(llvm)
    build_dir = install_root / "phasar" / f"build-{tag}-clang"
    install_dir = install_root / "phasar" / f"install-{tag}"
    commands: list[CommandResult] = []
    record: dict[str, Any] = {
        "url": PHASAR_URL,
        "ref": ref,
        "source_dir": str(source_dir),
        "build_dir": str(build_dir),
        "install_dir": str(install_dir),
        "status": "failed",
        "tools": {},
        "llvm_tools": llvm_tools(llvm),
    }

    try:
        commands.extend(
            git_clone_or_fetch(
                url=PHASAR_URL,
                source_dir=source_dir,
                ref=ref,
                timeout=timeout,
                recursive=True,
            )
        )
        record["patched_lifetimebound_macro"] = patch_phasar_compat(source_dir)
        build_dir.mkdir(parents=True, exist_ok=True)
        install_dir.mkdir(parents=True, exist_ok=True)
        llvm_version = phasar_llvm_version(llvm)
        llvm_bindir = Path(str(llvm.get("bindir", "")))
        cmake_args = [
            str(cmake),
            "-S",
            str(source_dir),
            "-B",
            str(build_dir),
            "-DCMAKE_BUILD_TYPE=Release",
            f"-DCMAKE_INSTALL_PREFIX={install_dir}",
            f"-DLLVM_DIR={llvm['cmake_dir']}",
            f"-DCMAKE_C_COMPILER={llvm_bindir / 'clang'}",
            f"-DCMAKE_CXX_COMPILER={llvm_bindir / 'clang++'}",
            f"-DPHASAR_LLVM_VERSION={llvm_version}",
            f"-Dclang={llvm_bindir / 'clang'}",
            f"-Dclangcpp={llvm_bindir / 'clang++'}",
            f"-Dopt={llvm_bindir / 'opt'}",
            "-DPHASAR_ALLOW_LTO_IN_RELEASE_BUILD=OFF",
            "-DPHASAR_BUILD_DOC=OFF",
            "-DPHASAR_BUILD_TESTS=OFF",
            "-DPHASAR_BUILD_UNITTESTS=OFF",
        ]
        commands.append(
            run_command(cmake_args, cwd=install_root, timeout=timeout, env=cmake_env(llvm))
        )
        commands.append(
            run_command(
                [str(cmake), "--build", str(build_dir), "--target", "phasar-cli", "-j", str(jobs)],
                cwd=install_root,
                timeout=timeout,
                env=cmake_env(llvm),
                check=False,
            )
        )
        if commands[-1].returncode != 0:
            commands.append(
                run_command(
                    [str(cmake), "--build", str(build_dir), "-j", str(jobs)],
                    cwd=install_root,
                    timeout=timeout,
                    env=cmake_env(llvm),
                )
            )
        commands.append(
            run_command(
                [str(cmake), "--install", str(build_dir)],
                cwd=install_root,
                timeout=timeout,
                env=cmake_env(llvm),
                check=False,
            )
        )
        tools = discover_tool(
            ["phasar-cli", "phasar-llvm", "phasar"],
            [install_dir / "bin", build_dir / "bin", build_dir, source_dir],
        )
        if not tools:
            raise InstallError("PhASAR build finished but no CLI binary was found")
        record.update({"status": "available", "tools": tools})
    except InstallError as exc:
        record["error"] = str(exc)
        record["tools"] = discover_tool(
            ["phasar-cli", "phasar-llvm", "phasar"], [install_dir, build_dir]
        )

    record["commit"] = git_commit(source_dir, timeout=timeout)
    record["commands"] = [command_record(command) for command in commands]
    return record


def detect_existing(llvm: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {
        "svf": {
            "status": "available" if discover_tool(["wpa", "svf-ex"], []) else "missing",
            "tools": discover_tool(["wpa", "svf-ex", "llvm2svf", "svf-devirt-oracle"], []),
            "llvm_tools": llvm_tools(llvm),
        },
        "phasar": {
            "status": "available"
            if discover_tool(["phasar-cli", "phasar-llvm", "phasar"], [])
            else "missing",
            "tools": discover_tool(["phasar-cli", "phasar-llvm", "phasar"], []),
            "llvm_tools": llvm_tools(llvm),
        },
    }


def write_manifest(path: Path, manifest: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")


def load_existing_manifest(path: Path) -> dict[str, Any]:
    try:
        data = json.loads(path.read_text())
    except (FileNotFoundError, json.JSONDecodeError):
        return {}
    return data if isinstance(data, dict) else {}


def ensure_svf_devirt_oracle(
    record: dict[str, Any],
    *,
    install_root: Path,
    llvm: dict[str, Any],
    timeout: int,
) -> dict[str, Any]:
    tools = record.get("tools", {})
    if not isinstance(tools, dict):
        tools = {}
    source = _repo_root() / "tools" / "svf_devirt_oracle.cpp"
    for name in ("svf-devirt-oracle", "svf-local-devirt"):
        value = tools.get(name)
        if isinstance(value, str):
            path = Path(value)
            if path.exists() and source.exists() and path.stat().st_mtime >= source.stat().st_mtime:
                return record
    if record.get("status") != "available":
        return record

    source_dir = Path(str(record.get("source_dir", "")))
    build_dir = Path(str(record.get("build_dir", "")))
    install_dir = Path(str(record.get("install_dir", "")))
    if not source_dir.exists() or not build_dir.exists() or not install_dir.exists():
        record = dict(record)
        record["svf_devirt_oracle_error"] = (
            "SVF is available but source/build/install directories are not recorded; "
            "rerun without --detect-only to build svf-devirt-oracle"
        )
        return record

    record = dict(record)
    try:
        oracle_tools, oracle_commands = build_svf_devirt_oracle(
            install_root=install_root,
            llvm=llvm,
            source_dir=source_dir,
            build_dir=build_dir,
            install_dir=install_dir,
            timeout=timeout,
        )
        updated_tools = dict(tools)
        updated_tools.update(oracle_tools)
        record["tools"] = updated_tools
        existing_commands = record.get("commands", [])
        if not isinstance(existing_commands, list):
            existing_commands = []
        record["commands"] = [
            *existing_commands,
            *(command_record(command) for command in oracle_commands),
        ]
    except InstallError as exc:
        record["svf_devirt_oracle_error"] = str(exc)
    return record


def make_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=_repo_root())
    parser.add_argument("--install-root", type=Path, default=Path("build/devirt-analyzers"))
    parser.add_argument("--manifest", type=Path, default=None)
    parser.add_argument("--llvm-config", default="/usr/lib/llvm-22/bin/llvm-config")
    parser.add_argument("--svf-llvm-config", default=None)
    parser.add_argument("--phasar-llvm-config", default=None)
    parser.add_argument("--cmake", default=None, help="CMake binary to use for analyzer builds")
    parser.add_argument("--svf-ref", default="SVF-3.2")
    parser.add_argument("--phasar-ref", default="development")
    parser.add_argument("--jobs", type=int, default=max(1, min(4, os.cpu_count() or 1)))
    parser.add_argument("--timeout", type=int, default=1800)
    parser.add_argument(
        "--only",
        action="append",
        choices=("svf", "phasar"),
        help="install only selected analyzer; may be repeated",
    )
    parser.add_argument(
        "--detect-only",
        action="store_true",
        help="write a manifest for analyzers already on PATH without cloning/building",
    )
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = make_arg_parser()
    args = parser.parse_args(argv)
    repo_root = args.repo_root.resolve()
    install_root = args.install_root
    if not install_root.is_absolute():
        install_root = repo_root / install_root
    manifest_path = args.manifest or (install_root / "manifest.json")
    if not manifest_path.is_absolute():
        manifest_path = repo_root / manifest_path

    try:
        llvm_config = resolve_program(args.llvm_config, "llvm-config")
        svf_llvm_config = resolve_program(args.svf_llvm_config, "llvm-config") if args.svf_llvm_config else llvm_config
        phasar_llvm_config = (
            resolve_program(args.phasar_llvm_config, "llvm-config")
            if args.phasar_llvm_config
            else llvm_config
        )
        cmake = resolve_program(args.cmake, "cmake")
        llvm = llvm_info(llvm_config, timeout=args.timeout)
        svf_llvm = llvm_info(svf_llvm_config, timeout=args.timeout)
        phasar_llvm = llvm_info(phasar_llvm_config, timeout=args.timeout)
        cmake_record = cmake_info(cmake, timeout=args.timeout)
    except InstallError as exc:
        parser.error(str(exc))

    requested = set(args.only or ("svf", "phasar"))
    install_root.mkdir(parents=True, exist_ok=True)
    existing = load_existing_manifest(manifest_path)
    existing_analyzers = existing.get("analyzers", {})
    if not isinstance(existing_analyzers, dict):
        existing_analyzers = {}
    detected = {
        "svf": detect_existing(svf_llvm)["svf"],
        "phasar": detect_existing(phasar_llvm)["phasar"],
    }
    manifest: dict[str, Any] = {
        "schema_version": 1,
        "install_root": str(install_root),
        "llvm": llvm,
        "cmake": cmake_record,
        "analyzers": {
            "svf": existing_analyzers.get("svf", detected["svf"]),
            "phasar": existing_analyzers.get("phasar", detected["phasar"]),
        },
    }

    if not args.detect_only:
        if "svf" in requested and manifest["analyzers"]["svf"]["status"] != "available":
            manifest["analyzers"]["svf"] = build_svf(
                install_root=install_root,
                llvm=svf_llvm,
                cmake=cmake,
                ref=args.svf_ref,
                jobs=args.jobs,
                timeout=args.timeout,
            )
            write_manifest(manifest_path, manifest)
        if "svf" in requested and manifest["analyzers"]["svf"]["status"] == "available":
            manifest["analyzers"]["svf"] = ensure_svf_devirt_oracle(
                manifest["analyzers"]["svf"],
                install_root=install_root,
                llvm=svf_llvm,
                timeout=args.timeout,
            )
            write_manifest(manifest_path, manifest)
        if "phasar" in requested and manifest["analyzers"]["phasar"]["status"] != "available":
            manifest["analyzers"]["phasar"] = build_phasar(
                install_root=install_root,
                llvm=phasar_llvm,
                cmake=cmake,
                ref=args.phasar_ref,
                jobs=args.jobs,
                timeout=args.timeout,
            )
            write_manifest(manifest_path, manifest)

    write_manifest(manifest_path, manifest)
    print(manifest_path)
    for name, record in manifest["analyzers"].items():
        tools = ", ".join(sorted(record.get("tools", {}).keys())) or "no tools"
        print(f"{name}: {record.get('status')} ({tools})")
    failed = [
        name
        for name, record in manifest["analyzers"].items()
        if name in requested and record.get("status") != "available"
    ]
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())

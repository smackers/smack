#!/usr/bin/env python3
"""Run the CMake wheel installed under build/devirt-analyzers/cmake-prefix."""

from __future__ import annotations

import os
import sys
from pathlib import Path


def main() -> None:
    repo_root = Path(__file__).resolve().parents[1]
    prefix = repo_root / "build" / "devirt-analyzers" / "cmake-prefix"
    site_packages = prefix / f"lib/python{sys.version_info.major}.{sys.version_info.minor}/site-packages"
    pythonpath = os.environ.get("PYTHONPATH")
    os.environ["PYTHONPATH"] = (
        f"{site_packages}{os.pathsep}{pythonpath}" if pythonpath else str(site_packages)
    )
    os.execv(sys.executable, [sys.executable, "-m", "cmake", *sys.argv[1:]])


if __name__ == "__main__":
    main()

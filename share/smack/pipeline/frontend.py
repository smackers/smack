"""Source-language frontend: drive each input through its language-specific
clang/lowering frontend and link the resulting bitcode.

Extracted from share/smack/top.py during Phase B5 of the modernization plan.
Depends only on the language-frontend table in `smack.frontend` and shell
helpers from `smack.utils` — no coupling back to `smack.top`.
"""

from __future__ import annotations

import argparse
import re
from pathlib import Path

from smack.frontend import extra_libs, frontends, languages, link_bc_files
from smack.utils import llvm_exact_bin, temporary_file, try_command


def target_selection(args: argparse.Namespace) -> None:
    """Determine the target architecture based on flags and source files."""
    # TODO more possible clang flags that determine the target?
    if not re.search("-target", args.clang_options):
        src: str = args.input_files[0]
        if Path(src).suffix == ".bc":
            ll = temporary_file(Path(src).stem, ".ll", args)
            try_command([llvm_exact_bin("llvm-dis"), "-o", ll, src])
            src = ll
        if Path(src).suffix == ".ll":
            with Path(src).open() as f:
                for line in f:
                    triple = re.findall('^target triple = "(.*)"', line)
                    if len(triple) > 0:
                        args.clang_options += f" -target {triple[0]}"
                        break


def frontend(args: argparse.Namespace) -> str | None:
    """Generate the LLVM bitcode file. Returns the linked .bc path, or None
    when the frontend short-circuits the pipeline (boogie / svcomp / json)."""
    bitcodes: list[str] = []
    libs: set[str] = set()
    noreturning_frontend = False

    def add_libs(lang: str) -> None:
        if lang in extra_libs():
            libs.add(extra_libs()[lang])

    if args.language:
        lang = languages()[args.language]
        if lang in ["boogie", "svcomp", "json"]:
            noreturning_frontend = True

        add_libs(lang)
        frontend_fn = frontends()[lang]
        for input_file in args.input_files:
            bitcode = frontend_fn(input_file, args)
            if bitcode is not None:
                bitcodes.append(bitcode)

    else:
        for input_file in args.input_files:
            lang = languages()[Path(input_file).suffix[1:]]
            if lang in ["boogie", "svcomp", "json"]:
                noreturning_frontend = True

            add_libs(lang)
            bitcode = frontends()[lang](input_file, args)
            if bitcode is not None:
                bitcodes.append(bitcode)

    if not noreturning_frontend:
        # link_bc_files is untyped today; coerce its result to str/None.
        result = link_bc_files(bitcodes, libs, args)
        return None if result is None else str(result)
    return None

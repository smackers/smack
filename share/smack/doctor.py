#!/usr/bin/env python3
#
# This file is distributed under the MIT License. See LICENSE for details.
#

import argparse
import os
import sys
from pathlib import Path
from subprocess import PIPE, Popen

from .versions import LLVM_SHORT_VERSION


def red(text):
    return '\033[0;31m' + text + '\033[0m'


def green(text):
    return '\033[0;32m' + text + '\033[0m'


def check(text, condition):
    global args
    global count
    if condition:
        if not args.quiet:
            print(green("[X] " + text))
    else:
        print(red("[-] " + text), file=sys.stderr)
        count += 1


def full_path(program):
    for path in os.environ['PATH'].split(os.pathsep):
        path = path.strip('"')
        exe = Path(path) / program
        if exe.is_file() and os.access(exe, os.X_OK):
            return str(exe)
    return None


def check_command(cmd):
    exe = full_path(cmd)

    check(f"{cmd} is in the path", exe is not None)
    if exe is not None:
        try:
            rc = Popen(cmd, stdout=PIPE, stderr=PIPE).wait()
        except BaseException:
            rc = None
        check(f"{cmd} is executable", rc in [0, 1, 2])


def check_version_command(cmd, version_arg):
    exe = full_path(cmd)

    check(f"{cmd} is in the path", exe is not None)
    if exe is not None:
        try:
            rc = Popen([cmd, version_arg], stdout=PIPE, stderr=PIPE).wait()
        except BaseException:
            rc = None
        check(f"{cmd} reports a version", rc == 0)


def check_verifier(cmd):
    if cmd == "corral" and os.environ.get("SMACK_ENABLE_CORRAL_TESTS") != "1":
        if not args.quiet:
            print("Skipping legacy Corral checks.")
        return

    exe = full_path(cmd)
    var = cmd.upper()

    if exe is not None:
        try:
            exe_text = Path(exe).read_text(encoding='utf-8')
        except UnicodeDecodeError:
            exe_text = None
        if exe_text is not None:
            check(f"{cmd} is a bash script", '#!/bin/bash' in exe_text)
            check(f"{cmd} redirects to {var}", (f"${var} \"$@\"") in exe_text)

    if var in os.environ:
        check(f"{var} environment variable is set", True)
        # Boogie/Corral ship as .NET tools installed via `dotnet tool install`;
        # the environment variable points directly at the executable wrapper
        # the dotnet tool layout drops in $TOOL_PATH (no `mono ...` prefix).
        verifier_exe = os.environ[var].split()[0]
        check(f"{var} verifier executable exists", Path(verifier_exe).is_file())

    if cmd == "boogie":
        check_version_command(cmd, "/version")
    else:
        check_command(cmd)


def check_headers(prefix):
    HEADERS = [
        (["share", "smack", "include", "smack.h"], "#define SMACK_H_"),
        (["share", "smack", "lib", "smack.c"], "void __SMACK_decls(void)"),
    ]

    for path, content in HEADERS:
        file = Path(prefix, *path)
        check(f"{file} exists", file.is_file())
        if file.is_file():
            check(f"{file} contains {content}", content in file.read_text())


def main():
    global args
    global count
    parser = argparse.ArgumentParser(description='Diagnose SMACK configuration issues.')
    parser.add_argument(
        '-q',
        '--quiet',
        dest='quiet',
        action="store_true",
        default=False,
        help='only show failed diagnostics',
    )
    parser.add_argument(
        '--prefix',
        metavar='P',
        dest='prefix',
        type=str,
        default='',
        help='point to the installation prefix',
    )
    args = parser.parse_args()
    count = 0

    if not args.quiet:
        print("Checking front-end dependencies...")
    check_version_command(f"clang-{LLVM_SHORT_VERSION}", "--version")
    check_version_command(f"clang++-{LLVM_SHORT_VERSION}", "--version")
    check_version_command(f"llvm-config-{LLVM_SHORT_VERSION}", "--version")
    check_version_command(f"llvm-link-{LLVM_SHORT_VERSION}", "--version")

    if not args.quiet:
        print("Checking back-end dependencies...")
    check_verifier("boogie")
    check_verifier("corral")

    if not args.quiet:
        print("Checking SMACK itself...")
    check_command("llvm2bpl")
    check_command("smack")

    if not args.prefix:
        check_headers(args.prefix)

    exit(count)

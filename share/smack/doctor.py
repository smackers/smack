#!/usr/bin/env python3
#
# This file is distributed under the MIT License. See LICENSE for details.
#

import os
from subprocess import Popen, PIPE
import sys
import re
import argparse


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
        exe = os.path.join(path, program)
        if os.path.isfile(exe) and os.access(exe, os.X_OK):
            return exe
    return None


def check_command(cmd):
    exe = full_path(cmd)

    check("%s is in the path" % cmd, exe is not None)
    if exe is not None:
        try:
            rc = Popen(cmd, stdout=PIPE, stderr=PIPE).wait()
        except BaseException:
            rc = None
        check("%s is executable" % cmd, rc == 1 or rc == 2)


def check_verifier(cmd):
    exe = full_path(cmd)
    var = cmd.upper()

    if exe is not None:
        check("%s is a bash script" % cmd, '#!/bin/bash' in open(exe).read())
        check(
            "%s redirects to %s" %
            (cmd, var), ("$%s \"$@\"" %
                         var) in open(exe).read())

    check("%s environment variable is set" % var, var in os.environ)
    if var in os.environ:
        check("%s invokes mono" % var, re.match(r'\Amono', os.environ[var]))
        verifier_exe = os.environ[var].split()[1]
        check("%s verifier executable exists" %
              var, os.path.isfile(verifier_exe))
        solver_exe = os.path.join(os.path.dirname(verifier_exe), "z3.exe")
        check("%s solver executable exists" % var, os.path.isfile(solver_exe))
        check("%s solver is executable" % var, os.access(solver_exe, os.X_OK))

    check_command(cmd)


def check_headers(prefix):
    HEADERS = [
        (["share", "smack", "include", "smack.h"], "#define SMACK_H_"),
        (["share", "smack", "lib", "smack.c"], "void __SMACK_decls()")
    ]

    for (path, content) in HEADERS:
        file = os.path.join(prefix, *path)
        check("%s exists" % file, os.path.isfile(file))
        if os.path.isfile(file):
            check(
                "%s contains %s" %
                (file, content), content in open(file).read())


def main():
    global args
    global count
    parser = argparse.ArgumentParser(
        description='Diagnose SMACK configuration issues.')
    parser.add_argument(
        '-q',
        '--quiet',
        dest='quiet',
        action="store_true",
        default=False,
        help='only show failed diagnostics')
    parser.add_argument(
        '--prefix',
        metavar='P',
        dest='prefix',
        type=str,
        default='',
        help='point to the installation prefix')
    args = parser.parse_args()
    count = 0

    if not args.quiet:
        print("Checking front-end dependencies...")
    check_command("clang")
    check_command("clang++")
    check_command("llvm-config")
    check_command("llvm-link")

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

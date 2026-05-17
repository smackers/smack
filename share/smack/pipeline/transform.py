"""External transform hooks: filter .bpl files and verifier output through
user-supplied subprocesses.

Extracted from share/smack/top.py during Phase B5 of the modernization plan.
Both functions are isolated subprocess.Popen sites; co-locating them here
makes the surface easy to audit / replace.
"""

import shlex
import subprocess
from pathlib import Path


def transform_bpl(args):
    """Filter args.bpl_file through args.transform_bpl in place."""
    if args.transform_bpl:
        with Path(args.bpl_file).open("r+") as bpl:
            old = bpl.read()
            bpl.seek(0)
            bpl.truncate()
            tx = subprocess.Popen(
                shlex.split(args.transform_bpl),
                stdin=subprocess.PIPE,
                stdout=bpl,
                universal_newlines=True,
            )
            tx.communicate(input=old)


def transform_out(args, old):
    """Pipe `old` through args.transform_out; return stdout (or `old` if no transform)."""
    out = old
    if args.transform_out:
        tx = subprocess.Popen(
            shlex.split(args.transform_out),
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            universal_newlines=True,
        )
        out, _err = tx.communicate(input=old)
    return out

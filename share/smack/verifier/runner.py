"""Single-verifier execution and result parsing.

Extracted from share/smack/top.py during Phase B5 of the modernization plan.
Houses `verification_result`, `process_verifier_output`, and `verify_bpl` —
the slice of the pipeline that runs one back-end verifier (Boogie/Corral/
Symbooglix) on a `.bpl` file and turns its stdout into a `VResult`.
"""

import re
from pathlib import Path

from smack.cli.results import VProperty, VResult
from smack.errtrace import error_trace, json_output_str
from smack.logging_config import get_warnings_logger
from smack.pipeline.transform import transform_out
from smack.replay import replay_error_trace
from smack.utils import try_command
from smack.verifier.commands import (
    boogie_command,
    corral_command,
)

_warn = get_warnings_logger()


def verification_result(verifier_output, verifier):
    if re.search(
        r"[1-9]\d* time out|Z3 ran out of resources|timed out|ERRORS_TIMEOUT",
        verifier_output,
    ):
        return VResult.TIMEOUT
    elif re.search(
        (r"[1-9]\d* verified, 0 errors?|no bugs|" r"NO_ERRORS_NO_TIMEOUT"),
        verifier_output,
    ):
        return VResult.VERIFIED
    elif re.search(
        (r"\d* verified, [1-9]\d* errors?|can fail|" r"ERRORS_NO_TIMEOUT"),
        verifier_output,
    ):
        attr = None
        attr_pat = r"assert {:(.+)}"

        if verifier == "corral":
            corral_af_msg = re.search(rf"ASSERTION FAILS {attr_pat}", verifier_output)
            if corral_af_msg:
                attr = corral_af_msg.group(1)

        elif verifier == "boogie":
            boogie_af_msg = re.search(
                r"([\w#$~%.\/-]+)\((\d+),\d+\): "
                r"Error: (This assertion might not hold|"
                r"this assertion could not be proved)",
                verifier_output,
            )
            if boogie_af_msg and re.match(".*[.]bpl$", boogie_af_msg.group(1)):
                line_no = int(boogie_af_msg.group(2))
                with Path(boogie_af_msg.group(1)).open() as f:
                    assert_line = re.search(attr_pat, f.read().splitlines(True)[line_no - 1])
                    if assert_line:
                        attr = assert_line.group(1)
        else:
            _warn.warning("Unable to decide error type.")

        if attr is not None:
            for p in [
                *VProperty.mem_safe_subprops(),
                VProperty.INTEGER_OVERFLOW,
                VProperty.RUST_PANICS,
            ]:
                if p.boogie_attr() == attr:
                    return p.result()

        return VResult.ASSERTION_FAILURE
    else:
        return VResult.UNKNOWN


def process_verifier_output(args, verifier_output):
    verifier_output = transform_out(args, verifier_output)
    result = verification_result(verifier_output, args.verifier)

    if args.json_file:
        with Path(args.json_file).open("w") as f:
            f.write(json_output_str(result, verifier_output, args.verifier))

    if result in VResult.ERROR:
        error = error_trace(verifier_output, args.verifier)

        if args.error_file:
            with Path(args.error_file).open("w") as f:
                f.write(error)

        if not args.quiet:
            print(error)

        if args.replay:
            replay_error_trace(verifier_output, args)
    print(result.message(args))
    return result.return_code()


def verify_bpl(args):
    """Verify the Boogie source file with a back-end verifier."""

    if args.verifier == "boogie" or args.modular:
        command = boogie_command(args)
        command += ["/proverOpt:O:smt.array.extensional=false"]
        command += ["/proverOpt:O:smt.qi.eager_threshold=100"]
        command += ["/proverOpt:O:smt.arith.solver=2"]

    elif args.verifier == "corral":
        command = corral_command(args)
        command += ["/bopt:proverOpt:O:smt.qi.eager_threshold=100"]
        command += ["/bopt:proverOpt:O:smt.arith.solver=2"]

    if args.verifier_options:
        command += args.verifier_options.split()

    if args.verifier == "boogie" or args.modular:
        command += [args.bpl_file]

    verifier_output = try_command(command, timeout=args.time_limit)
    return process_verifier_output(args, verifier_output)

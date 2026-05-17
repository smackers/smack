"""Multi-verifier portfolio: launch several back-end verifiers in parallel
and return the first result.

Extracted from share/smack/top.py during Phase B5 of the modernization plan.
"""

import copy
import multiprocessing
from pathlib import Path

import yaml

from smack.logging_config import get_warnings_logger
from smack.utils import try_command
from smack.verifier.commands import (
    boogie_command,
    corral_command,
)
from smack.verifier.runner import process_verifier_output

_warn = get_warnings_logger()


def thread_verify_bpl(args, args_to_add):
    if "verifier" in args_to_add:
        if args_to_add["verifier"] == "portfolio":
            raise RuntimeError(
                "portfolio is not a valid verifier specification within the portfolio configuration"
            )
        else:
            _warn.warning(
                "Warning: SMACK is using argument verifier from the chosen portfolio configuration"
            )
            args.verifier = args_to_add["verifier"]
    else:
        raise RuntimeError("verifier is a required argument in the portfolio configuration file")

    if "modular" in args_to_add:
        if args.modular:
            raise RuntimeError(
                "argument modular specified in both command line and portfolio configuration"
            )
        else:
            _warn.warning(
                "Warning: SMACK is using argument modular from the chosen portfolio configuration"
            )
            args.modular = args_to_add["modular"]

    if (args.verifier != "boogie") and args.modular:
        raise RuntimeError("Incompatible arguments modular and non-boogie verifier were specified")

    if "verifier-options" in args_to_add:
        if args.verifier_options:
            raise RuntimeError(
                "argument verifier-options specified in both"
                " command line and portfolio configuration"
            )
        else:
            _warn.warning(
                "Warning: SMACK is using argument verifier-"
                "options from the chosen portfolio configuration"
            )
            args.verifier_options = args_to_add["verifier-options"]

    if args.verifier == "boogie" or args.modular:
        command = boogie_command(args)

    elif args.verifier == "corral":
        command = corral_command(args)

    if args.verifier_options:
        command += args.verifier_options.split()

    if args.verifier == "boogie" or args.modular:
        command += [args.bpl_file]

    verifier_output = try_command(command, timeout=args.time_limit)
    return args, verifier_output


def verify_bpl_portfolio(args):
    with Path(args.portfolio_config).open() as f:
        portfolio_config = yaml.safe_load(f)
    p = multiprocessing.Pool()
    results = {}  # map of process -> thread name

    for thread in list(portfolio_config.keys()):
        async_result = p.apply_async(
            thread_verify_bpl,
            args=(copy.deepcopy(args), portfolio_config[thread]),
        )
        results[async_result] = thread

    # TODO: revisit this loop to improve efficiency
    while True:
        for result in list(results.keys()):
            if result.ready():
                p.terminate()
                args, verifier_output = result.get()
                verifier_output = process_verifier_output(args, verifier_output)
                thread_name = results[result]
                _warn.warning(f"SMACK portfolio {thread_name} terminated")
                return verifier_output

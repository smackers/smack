import multiprocessing
import signal
import sys

# Phase B5: argparse + input/output validation moved to share/smack/cli/parser.py.
from .cli.parser import (  # noqa: F401
    FileAction,
    arguments,
    exit_with_error,
    validate_input_files,
    validate_output_file,
)

# VResult / VProperty / PropertyAction were extracted to share/smack/cli/results.py
# in Phase B5. Re-exported here for backwards compatibility with existing
# `from smack.top import VResult, VProperty` callers (svcomp/utils, errtrace,
# frontend, etc.).
from .cli.results import PropertyAction, VProperty, VResult  # noqa: F401

# Phase B5: VERSION + inlined_procedures hoisted to share/smack/constants.py.
from .constants import VERSION, inlined_procedures  # noqa: F401

# Phase B5: diffprod orchestration moved to share/smack/diffprod/orchestrate.py.
from .diffprod.orchestrate import (  # noqa: F401
    diff_product_patched_filename,
    diff_product_side_args,
    llvm_to_bpl_option_args,
    run_diff_product,
    run_paired_diff_product_lowering,
    verify_diff_product,
)

# Phase B5: target selection + frontend orchestration moved to share/smack/pipeline/frontend.py.
from .pipeline.frontend import frontend, target_selection

# Phase B5: subprocess.Popen transform hooks moved to share/smack/pipeline/transform.py.
from .pipeline.transform import transform_bpl, transform_out  # noqa: F401

# Phase B5: bpl-rewriting helpers + llvm_to_bpl orchestrator moved to
# share/smack/pipeline/translate.py.
from .pipeline.translate import (  # noqa: F401
    annotate_bpl,
    llvm_to_bpl,
    memsafety_subproperty_selection,
    procedure_annotation,
    replace_reach_error,
)
from .svcomp.utils import verify_bpl_svcomp
from .utils import (
    remove_temp_files,
)

# Phase B5: command-builders moved to share/smack/verifier/commands.py.
# Re-exported here so internal callers (verify_bpl, run_diff_product, etc.)
# keep working without touching every callsite.
from .verifier.commands import (  # noqa: F401
    boogie_command,
    corral_command,
)

# Phase B5: portfolio multi-verifier orchestration moved to share/smack/verifier/portfolio.py.
from .verifier.portfolio import thread_verify_bpl, verify_bpl_portfolio  # noqa: F401

# Phase B5: single-verifier execution moved to share/smack/verifier/runner.py.
from .verifier.runner import (  # noqa: F401
    process_verifier_output,
    verification_result,
    verify_bpl,
)


def clean_up_upon_sigterm(main):
    def handler(signum, frame):
        remove_temp_files_lock.acquire()
        remove_temp_files()
        remove_temp_files_lock.release()
        sys.exit(0)

    signal.signal(signal.SIGTERM, handler)
    return main


@clean_up_upon_sigterm
def main():
    try:
        global remove_temp_files_lock
        remove_temp_files_lock = multiprocessing.Lock()

        global args
        args = arguments()

        # Phase B3: configure smack logger hierarchy from --quiet/--verbose/--debug/--warn.
        from .logging_config import configure as _configure_logging

        _configure_logging(
            quiet=getattr(args, "quiet", False),
            verbose=getattr(args, "verbose", False),
            debug=getattr(args, "debug", False),
            warn=getattr(args, "warn", "approximate"),
        )

        if getattr(args, 'diff_product_mode', None):
            if not args.quiet:
                print(f"SMACK program verifier version {VERSION}")
            run_diff_product(args)
            return

        target_selection(args)

        if not args.quiet:
            print(f"SMACK program verifier version {VERSION}")

        frontend(args)

        if args.no_verify:
            if not args.quiet:
                print(f"SMACK generated {args.bpl_file}")
        else:
            if args.verifier == 'svcomp':
                verify_bpl_svcomp(args)
                return
            elif args.verifier == 'portfolio':
                return_code = verify_bpl_portfolio(args)
            else:
                return_code = verify_bpl(args)
            sys.exit(return_code)

    except KeyboardInterrupt:
        sys.exit("SMACK aborted by keyboard interrupt.")

    finally:
        remove_temp_files()

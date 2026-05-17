"""argparse setup + input/output validation for the SMACK CLI.

Extracted from share/smack/top.py during Phase B5 of the modernization plan.
`top.py` re-exports `arguments`, `FileAction`, `exit_with_error`, and the
validators so existing callers (including `main()`) keep working without
touching every callsite.
"""

import argparse
import os
import sys
from pathlib import Path

from smack.cli.results import PropertyAction, VProperty
from smack.constants import VERSION
from smack.frontend import frontends, languages
from smack.utils import smack_portfolio_path, temporary_file


class FileAction(argparse.Action):
    def __init__(self, option_strings, dest, **kwargs):
        super().__init__(option_strings, dest, **kwargs)

    def __call__(self, parser, namespace, values, option_string=None):
        if option_string is None:
            validate_input_files(values)
        else:
            # presumably output files (e.g., .bc, .ll, etc)
            validate_output_file(values)
        setattr(namespace, self.dest, values)


def exit_with_error(error):
    sys.exit(f'Error: {error}.')


def validate_input_files(files):
    def validate_input_file(file):
        """
        Check whether the given input file is valid, returning a reason if not.
        """

        p = Path(file)
        file_extension = p.suffix.lstrip(".")
        if not p.is_file():
            exit_with_error(f"Cannot find file {file}")

        if not os.access(file, os.R_OK):
            exit_with_error(f"Cannot read file {file}")

        elif file_extension not in languages():
            exit_with_error(f"Unexpected source file extension '{file_extension}'")

    list(map(validate_input_file, files))


def validate_output_file(file):
    dir_name = Path(file).resolve().parent
    if not dir_name.is_dir():
        exit_with_error(f"directory {dir_name} doesn't exist")
    if not os.access(dir_name, os.W_OK):
        exit_with_error(f"file {file} may not be writeable")
    # try:
    #  with open(file, 'w') as f:
    #    pass
    # except IOError:
    #  exit_with_error("file %s may not be writeable" % file)


def arguments():
    """Parse command-line arguments"""

    parser = argparse.ArgumentParser()

    parser.add_argument(
        'input_files',
        metavar='input-files',
        nargs='*',
        action=FileAction,
        type=str,
        help='source file to be translated/verified',
    )

    parser.add_argument('--version', action='version', version='SMACK version ' + VERSION)

    noise_group = parser.add_mutually_exclusive_group()

    noise_group.add_argument(
        '-q', '--quiet', action='store_true', default=False, help='enable quiet output'
    )

    noise_group.add_argument(
        '-v', '--verbose', action='store_true', default=False, help='enable verbose output'
    )

    noise_group.add_argument(
        '-d', '--debug', action="store_true", default=False, help='enable debugging output'
    )

    noise_group.add_argument(
        '--debug-only',
        metavar='MODULES',
        default=None,
        type=str,
        help='limit debugging output to given MODULES',
    )

    noise_group.add_argument(
        '--warn',
        default="approximate",
        choices=['silent', 'approximate', 'info'],
        help='''enable certain type of warning messages
            (silent: no warning messages;
            approximate: warnings about introduced approximations;
            info: warnings about introduced approximations and
            translation information)
            [default: %(default)s]''',
    )

    parser.add_argument(
        '-t',
        '--no-verify',
        action="store_true",
        default=False,
        help='perform only translation, without verification.',
    )

    parser.add_argument(
        '-w',
        '--error-file',
        metavar='FILE',
        default=None,
        type=str,
        help='save error trace/witness to FILE',
    )

    parser.add_argument(
        '--json-file', metavar='FILE', default=None, type=str, help='generate JSON output to FILE'
    )

    frontend_group = parser.add_argument_group('front-end options')

    frontend_group.add_argument(
        '-x',
        '--language',
        metavar='LANG',
        choices=list(frontends().keys()),
        default=None,
        help='Treat input files as having type LANG.',
    )

    frontend_group.add_argument(
        '-bc',
        '--bc-file',
        metavar='FILE',
        default=None,
        action=FileAction,
        type=str,
        help='save initial LLVM bitcode to FILE',
    )

    frontend_group.add_argument(
        '--linked-bc-file', metavar='FILE', default=None, type=str, help=argparse.SUPPRESS
    )

    frontend_group.add_argument(
        '--replay-harness',
        metavar='FILE',
        default='replay-harness.c',
        type=str,
        help=argparse.SUPPRESS,
    )

    frontend_group.add_argument(
        '--replay-exe-file', metavar='FILE', default='replay-exe', type=str, help=argparse.SUPPRESS
    )

    frontend_group.add_argument(
        '-ll',
        '--ll-file',
        metavar='FILE',
        default=None,
        action=FileAction,
        type=str,
        help='save final LLVM IR to FILE',
    )

    frontend_group.add_argument(
        '--clang-options',
        metavar='OPTIONS',
        default='',
        help='additional compiler arguments (e.g., --clang-options="-w -g")',
    )

    translate_group = parser.add_argument_group('translation options')

    translate_group.add_argument(
        '-bpl',
        '--bpl-file',
        metavar='FILE',
        default=None,
        action=FileAction,
        type=str,
        help='save (intermediate) Boogie code to FILE',
    )

    translate_group.add_argument(
        '--provenance-syms',
        action='store_true',
        default=False,
        help='include LLVM provenance annotations in generated Boogie code',
    )

    translate_group.add_argument(
        '--diff-product',
        metavar='PATCH',
        default=None,
        action=FileAction,
        type=str,
        help='build a diff-scoped product artifact from two source inputs',
    )

    translate_group.add_argument(
        '--product-mode',
        choices=['functions', 'patch'],
        default=None,
        help='easy diff-product interface: functions=two sources, patch=source plus diff',
    )

    translate_group.add_argument(
        '--functional-equivalence',
        action='store_true',
        default=False,
        help='build a structured diff-scoped product for functional equivalence '
        'from --source, --patch, and --entry',
    )

    translate_group.add_argument(
        '--left',
        metavar='FILE',
        default=None,
        action=FileAction,
        type=str,
        help='left source input for --product-mode functions',
    )

    translate_group.add_argument(
        '--right',
        metavar='FILE',
        default=None,
        action=FileAction,
        type=str,
        help='right source input for --product-mode functions',
    )

    translate_group.add_argument(
        '--source',
        metavar='FILE',
        default=None,
        action=FileAction,
        type=str,
        help='source input for --product-mode patch',
    )

    translate_group.add_argument(
        '--patch',
        metavar='FILE',
        default=None,
        action=FileAction,
        type=str,
        help='unified diff input for --product-mode patch',
    )

    translate_group.add_argument(
        '--entry',
        metavar='PROC',
        default=None,
        type=str,
        help='entry procedure for both product sides',
    )

    translate_group.add_argument(
        '--left-entry',
        metavar='PROC',
        default=None,
        type=str,
        help='left entry procedure for product mode',
    )

    translate_group.add_argument(
        '--right-entry',
        metavar='PROC',
        default=None,
        type=str,
        help='right entry procedure for product mode',
    )

    translate_group.add_argument(
        '--product-out',
        metavar='FILE',
        default=None,
        type=str,
        help='write the product Boogie artifact to FILE',
    )

    translate_group.add_argument(
        '--product-json',
        metavar='FILE',
        default=None,
        type=str,
        help='write product provenance/e-graph report to FILE',
    )

    translate_group.add_argument(
        '--diff-left',
        metavar='FILE',
        default=None,
        action=FileAction,
        type=str,
        help='left source input for --diff-product',
    )

    translate_group.add_argument(
        '--diff-right',
        metavar='FILE',
        default=None,
        action=FileAction,
        type=str,
        help='right source input for --diff-product',
    )

    translate_group.add_argument(
        '--diff-left-entry',
        metavar='PROC',
        default='main',
        type=str,
        help='left entry procedure for --diff-product [default: %(default)s]',
    )

    translate_group.add_argument(
        '--diff-right-entry',
        metavar='PROC',
        default=None,
        type=str,
        help='right entry procedure for --diff-product [default: left entry]',
    )

    translate_group.add_argument(
        '--diff-product-out',
        metavar='FILE',
        default=None,
        type=str,
        help='write the diff-product Boogie artifact to FILE',
    )

    translate_group.add_argument(
        '--diff-product-json',
        metavar='FILE',
        default=None,
        type=str,
        help='write source/Boogie impact and provenance report to FILE',
    )

    translate_group.add_argument(
        '--diff-product-match-json',
        metavar='FILE',
        default=None,
        type=str,
        help='write LLVM structural matcher report to FILE',
    )

    translate_group.add_argument(
        '--diff-product-left-bpl-out',
        metavar='FILE',
        default=None,
        type=str,
        help='write the paired-lowering left-side Boogie artifact to FILE',
    )

    translate_group.add_argument(
        '--diff-product-right-bpl-out',
        metavar='FILE',
        default=None,
        type=str,
        help='write the paired-lowering right-side Boogie artifact to FILE',
    )

    translate_group.add_argument(
        '--diff-product-dump-llvm',
        action='store_true',
        default=False,
        help='dump normalized left/right LLVM IR while building --diff-product',
    )

    translate_group.add_argument(
        '--diff-product-structured-bpl-loops',
        action='store_true',
        default=False,
        help='emit supported loops as structured Boogie while statements only '
        'during paired diff-product lowering',
    )

    translate_group.add_argument(
        '--diff-product-structured-bpl-loops-strict',
        action='store_true',
        default=False,
        help='fail paired diff-product lowering if any loop cannot be emitted as structured Boogie',
    )

    translate_group.add_argument(
        '--diff-product-alignment',
        choices=['auto', 'corerel', 'legacy', 'baseline'],
        default='auto',
        help='select diff-product alignment strategy [default: %(default)s]',
    )

    translate_group.add_argument(
        '--diff-product-no-egraph',
        action='store_true',
        default=False,
        help='disable e-graph optimization in --diff-product',
    )

    translate_group.add_argument(
        '--diff-product-egraph-timeout',
        metavar='N',
        default=10,
        type=int,
        help='e-graph timeout for --diff-product, in seconds [default: %(default)s]',
    )

    translate_group.add_argument(
        '--diff-product-require-actual',
        action='store_true',
        default=False,
        help='fail if --diff-product can only emit metadata fallback',
    )

    translate_group.add_argument(
        '--diff-product-verify',
        action='store_true',
        default=False,
        help='run the selected diff-product through the configured verifier',
    )

    translate_group.add_argument(
        '--rewrite-bitwise-ops',
        action="store_true",
        default=False,
        help='''attempts to provide models for bitwise operations
                when integer encoding is used''',
    )

    translate_group.add_argument(
        '--no-memory-splitting',
        action="store_true",
        default=False,
        help='disable region-based memory splitting',
    )

    translate_group.add_argument(
        '--sea-dsa-mode',
        choices=['ci', 'bu', 'butd-cs', 'cs', 'flat'],
        default='bu',
        help='select SeaDsa analysis mode for memory partitioning [default: %(default)s]',
    )

    translate_group.add_argument(
        '--sea-dsa-type-aware',
        action="store_true",
        default=False,
        help='enable SeaDsa type-aware mode (experimental)',
    )

    translate_group.add_argument(
        '--memory-partitioner',
        choices=['sea-dsa', 'cell-refined', 'aa-refined', 'svf-refined', 'svf-native'],
        default='sea-dsa',
        help='select SMACK memory partitioner [default: %(default)s]',
    )

    translate_group.add_argument(
        '--memory-partition-oracle',
        metavar='FILE',
        default=None,
        help='read external memory partition oracle JSON',
    )

    translate_group.add_argument(
        '--svf-wpa',
        metavar='FILE',
        default=None,
        help='SVF wpa executable for auto-generating SVF memory oracles '
        '[default: SMACK_SVF_WPA or wpa]',
    )

    translate_group.add_argument(
        '--svf-extapi',
        metavar='FILE',
        default=None,
        help='SVF extapi.bc path for SVF oracle generation or in-process svf-native '
        '[default: SMACK_SVF_EXTAPI]',
    )

    translate_group.add_argument(
        '--svf-mem-par',
        choices=['distinct', 'intra-disjoint', 'inter-disjoint'],
        default=None,
        help='SVF MemorySSA partition mode for SVF oracle generation or in-process svf-native '
        '[default: SMACK_SVF_MEM_PAR or intra-disjoint]',
    )

    translate_group.add_argument(
        '--svf-analysis',
        choices=['ander'],
        default=None,
        help='SVF pointer analysis for in-process svf-native [default: ander]',
    )

    translate_group.add_argument(
        '--svf-timeout',
        metavar='N',
        default=None,
        type=int,
        help='SVF oracle-generation timeout in seconds '
        '[default: SMACK_SVF_TIMEOUT or 300]',
    )

    translate_group.add_argument(
        '--svf-loop-frames',
        action='store_true',
        default=False,
        help='emit SVF-derived loop frame invariants when complete',
    )

    translate_group.add_argument(
        '--svf-call-frames',
        action='store_true',
        default=False,
        help='enable SVF callsite frame facts where supported',
    )

    translate_group.add_argument(
        '--svf-indirect-calls',
        action='store_true',
        default=False,
        help='collect SVF indirect-call target facts in generated oracles',
    )

    translate_group.add_argument(
        '--svf-loop-diagnostics',
        action='store_true',
        default=False,
        help='collect SVF loop diagnostics in generated oracles',
    )

    translate_group.add_argument(
        '--svf-saber-diagnostics',
        action='store_true',
        default=False,
        help='reserve SVF SABER diagnostic collection in generated oracles',
    )

    translate_group.add_argument(
        '--svf-mta-diagnostics',
        action='store_true',
        default=False,
        help='reserve SVF MTA diagnostic collection in generated oracles',
    )

    translate_group.add_argument(
        '--memory-partition-report',
        metavar='FILE',
        default=None,
        help='write memory partitioning report JSON',
    )

    translate_group.add_argument(
        '--devirt-report',
        metavar='FILE',
        default=None,
        help='write indirect-call devirtualization report JSON',
    )

    translate_group.add_argument(
        '--static-init-zero-memset-threshold',
        metavar='N',
        default=None,
        type=int,
        help='emit all-zero static initializers of at least N bytes as compact '
        'memset summaries; 0 disables this optimization',
    )

    translate_group.add_argument(
        '--mem-mod',
        choices=['no-reuse', 'no-reuse-impls', 'reuse'],
        default='no-reuse-impls',
        help='''select memory model
                (no-reuse=never reallocate the same address,
                reuse=reallocate freed addresses) [default: %(default)s]''',
    )

    translate_group.add_argument(
        '--static-unroll',
        action="store_true",
        default=False,
        help='enable static LLVM loop unrolling pass as a preprocessing step',
    )

    translate_group.add_argument(
        '--pthread', action='store_true', default=False, help='enable support for pthread programs'
    )

    translate_group.add_argument(
        '--max-threads',
        default='32',
        type=int,
        help='bound on the number of threads [default: %(default)s]',
    )

    translate_group.add_argument(
        '--integer-encoding',
        choices=['bit-vector', 'unbounded-integer', 'wrapped-integer'],
        default='unbounded-integer',
        help='''machine integer encoding
                (bit-vector=use SMT bit-vector theory,
                unbounded-integer=use SMT integer theory,
                wrapped-integer=use SMT integer theory but model wrap-around
                behavior) [default: %(default)s]''',
    )

    translate_group.add_argument(
        '--timing-annotations', action="store_true", default=False, help='enable timing annotations'
    )

    translate_group.add_argument(
        '--pointer-encoding',
        choices=['bit-vector', 'unbounded-integer'],
        default='unbounded-integer',
        help='''pointer encoding
                (bit-vector=use SMT bit-vector theory,
                ubounded-integer=use SMT integer theory)
                [default: %(default)s]''',
    )

    translate_group.add_argument(
        '--no-byte-access-inference',
        action="store_true",
        default=False,
        help='disable bit-precision-related optimizations with DSA',
    )

    translate_group.add_argument(
        '--entry-points',
        metavar='PROC',
        nargs='+',
        default=['main'],
        help='specify top-level procedures [default: %(default)s]',
    )

    translate_group.add_argument(
        '--checked-functions',
        metavar='PROC',
        nargs='+',
        default=[],
        help='''specify functions on which to do property checking.
                These can be specified as extended regular expressions.
                NOTE: a regular expression must match the entire
                function name. [default: everything]''',
    )

    translate_group.add_argument(
        '--check',
        metavar='PROPERTY',
        nargs='+',
        choices=list(VProperty),
        default=VProperty.NONE,
        type=VProperty.argparse,
        action=PropertyAction,
        help='''select properties to check
                [choices: %(choices)s; default: assertions]
                (note that memory-safety is the union of valid-deref,
                valid-free, memleak)''',
    )

    translate_group.add_argument(
        '--llvm-assumes',
        choices=['none', 'use', 'check'],
        default='none',
        help='''optionally enable generation of Boogie assume statements from
                LLVM assume statements (none=no generation [default],
                use=generate assume statements,
                check=check assume statements)''',
    )

    translate_group.add_argument(
        '--float',
        action="store_true",
        default=False,
        help='enable bit-precise floating-point functions',
    )

    translate_group.add_argument(
        '--strings', action='store_true', default=False, help='enable support for string'
    )

    translate_group.add_argument(
        '--fail-on-loop-exit',
        action='store_true',
        default=False,
        help='''Add assert false to the end of each loop
                (useful for deciding how much unroll to use)''',
    )

    verifier_group = parser.add_argument_group('verifier options')

    verifier_group.add_argument(
        '--verifier',
        choices=['boogie', 'corral', 'portfolio', 'svcomp'],
        default='boogie',
        help='back-end verification engine',
    )

    verifier_group.add_argument(
        '--solver', choices=['z3'], default='z3', help='back-end SMT solver'
    )

    verifier_group.add_argument(
        '--portfolio-config',
        metavar='FILE',
        default=smack_portfolio_path(),
        action=FileAction,
        type=str,
        help='read portfolio configuration in YAML format from FILE',
    )

    verifier_group.add_argument(
        '--unroll',
        metavar='N',
        default='1',
        type=lambda x: int(x) if int(x) > 0 else parser.error('Unroll bound has to be positive.'),
        help='loop/recursion unroll bound [default: %(default)s]',
    )

    verifier_group.add_argument(
        '--loop-limit',
        metavar='N',
        default='1',
        type=int,
        help='upper bound on minimum loop iterations [default: %(default)s]',
    )

    verifier_group.add_argument(
        '--context-bound',
        metavar='K',
        default='1',
        type=int,
        help='''bound on the number of thread contexts in Corral
                [default: %(default)s]''',
    )

    verifier_group.add_argument(
        '--verifier-options',
        metavar='OPTIONS',
        default='',
        help='''additional verifier arguments
                (e.g., --verifier-options="/trackAllVars /staticInlining")''',
    )

    verifier_group.add_argument(
        '--time-limit',
        metavar='N',
        default='1200',
        type=int,
        help='verifier time limit, in seconds [default: %(default)s]',
    )

    verifier_group.add_argument(
        '--max-violations',
        metavar='N',
        default='1',
        type=int,
        help='maximum reported assertion violations [default: %(default)s]',
    )

    verifier_group.add_argument(
        '--svcomp-property',
        metavar='FILE',
        default=None,
        type=str,
        help='load SVCOMP property to check from FILE',
    )

    verifier_group.add_argument(
        '--modular',
        action="store_true",
        default=False,
        help='''enable contracts-based modular deductive verification
                (uses Boogie)''',
    )

    verifier_group.add_argument(
        '--replay',
        action="store_true",
        default=False,
        help='enable replay of error trace with test harness.',
    )

    plugins_group = parser.add_argument_group('plugins')

    plugins_group.add_argument(
        '--transform-bpl',
        metavar='COMMAND',
        default=None,
        type=str,
        help='transform generated Boogie code via COMMAND',
    )

    plugins_group.add_argument(
        '--transform-out',
        metavar='COMMAND',
        default=None,
        type=str,
        help='transform verifier output via COMMAND',
    )

    args = parser.parse_args()

    explicit_bpl_file = args.bpl_file is not None

    if args.product_out and args.diff_product_out is None:
        args.diff_product_out = args.product_out
    if args.product_json and args.diff_product_json is None:
        args.diff_product_json = args.product_json

    if args.functional_equivalence:
        if args.product_mode is not None and args.product_mode != 'patch':
            parser.error(
                '--functional-equivalence cannot be combined with --product-mode functions'
            )
        args.product_mode = 'patch'
        if not (
            args.diff_product_structured_bpl_loops or args.diff_product_structured_bpl_loops_strict
        ):
            args.diff_product_structured_bpl_loops = True

    if args.product_mode == 'functions':
        if not args.left or not args.right:
            parser.error('--product-mode functions requires --left and --right')
        args.diff_product_mode = 'functions'
        args.diff_left = args.left
        args.diff_right = args.right
        left_entry = args.left_entry or args.entry or args.diff_left_entry
        right_entry = args.right_entry or args.entry or args.diff_right_entry
        args.diff_left_entry = left_entry
        args.diff_right_entry = right_entry or left_entry
    elif args.product_mode == 'patch':
        if not args.source or not args.patch:
            parser.error('--product-mode patch requires --source and --patch')
        args.diff_product_mode = 'patch'
        args.diff_product = args.patch
        args.diff_left = args.source
        left_entry = args.left_entry or args.entry or args.diff_left_entry
        right_entry = args.right_entry or args.entry or args.diff_right_entry
        args.diff_left_entry = left_entry
        args.diff_right_entry = right_entry or left_entry
    elif args.diff_product:
        args.diff_product_mode = 'patch-with-right'
    else:
        args.diff_product_mode = None

    if (
        args.diff_product_structured_bpl_loops or args.diff_product_structured_bpl_loops_strict
    ) and not args.diff_product_mode:
        parser.error(
            '--diff-product-structured-bpl-loops is only valid in --diff-product or --product-mode'
        )

    if args.diff_product_mode:
        if args.diff_product_mode == 'patch-with-right' and (
            not args.diff_left or not args.diff_right
        ):
            parser.error('--diff-product requires --diff-left and --diff-right')
        if args.diff_right_entry is None:
            args.diff_right_entry = args.diff_left_entry
        side_bpl_out_requested = args.diff_product_left_bpl_out or args.diff_product_right_bpl_out
        if args.diff_product_out is None and not side_bpl_out_requested:
            args.diff_product_out = args.bpl_file if explicit_bpl_file else 'diff-product.bpl'
        if args.bpl_file is None and args.diff_product_out is not None:
            args.bpl_file = args.diff_product_out
        args.no_verify = True
    elif not args.input_files:
        parser.error('input-files are required unless product mode is used')

    if not args.bc_file:
        args.bc_file = temporary_file('a', '.bc', args)

    if not args.linked_bc_file:
        args.linked_bc_file = temporary_file('b', '.bc', args)

    if not args.bpl_file:
        args.bpl_file = 'a.bpl' if args.no_verify else temporary_file('a', '.bpl', args)

    if args.check == VProperty.NONE:
        args.check = VProperty.ASSERTIONS

    # TODO are we (still) using this?
    # with open(args.input_file, 'r') as f:
    #   for line in f.readlines():
    #     m = re.match('.*SMACK-OPTIONS:[ ]+(.*)$', line)
    #     if m:
    #       return args = parser.parse_args(m.group(1).split() + sys.argv[1:])

    return args

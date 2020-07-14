import argparse
import errno
import io
import json
import os
import platform
import re
import shutil
import sys
import shlex
import subprocess
import signal
import functools
from .svcomp.utils import verify_bpl_svcomp
from .utils import temporary_file, try_command, remove_temp_files
from .replay import replay_error_trace
from .frontend import link_bc_files, frontends, languages, extra_libs

VERSION = '2.4.1'


def results(args):
    """A dictionary of the result output messages."""
    return {
        'verified': 'SMACK found no errors.' if args.modular else 'SMACK found no errors with unroll bound %s.' % args.unroll,
        'error': 'SMACK found an error.',
        'invalid-deref': 'SMACK found an error: invalid pointer dereference.',
        'invalid-free': 'SMACK found an error: invalid memory deallocation.',
        'invalid-memtrack': 'SMACK found an error: memory leak.',
        'overflow': 'SMACK found an error: integer overflow.',
        'timeout': 'SMACK timed out.',
        'unknown': 'SMACK result is unknown.'}


def inlined_procedures():
    return [
        '$galloc',
        '$alloc',
        '$malloc',
        '$free',
        '$memset',
        '$memcpy',
        '__VERIFIER_',
        '$initialize',
        '__SMACK_static_init',
        '__SMACK_init_func_memory_model',
        '__SMACK_check_overflow'
    ]


class FileAction(argparse.Action):
    def __init__(self, option_strings, dest, **kwargs):
        super(FileAction, self).__init__(option_strings, dest, **kwargs)

    def __call__(self, parser, namespace, values, option_string=None):
        if option_string is None:
            validate_input_files(values)
        else:
            # presumably output files (e.g., .bc, .ll, etc)
            validate_output_file(values)
        setattr(namespace, self.dest, values)


def exit_with_error(error):
    sys.exit('Error: %s.' % error)


def validate_input_files(files):
    def validate_input_file(file):
        """Check whether the given input file is valid, returning a reason if not."""

        file_extension = os.path.splitext(file)[1][1:]
        if not os.path.isfile(file):
            exit_with_error("Cannot find file %s" % file)

        if not os.access(file, os.R_OK):
            exit_with_error("Cannot read file %s" % file)

        elif file_extension not in languages():
            exit_with_error(
                "Unexpected source file extension '%s'" %
                file_extension)
    list(map(validate_input_file, files))


def validate_output_file(file):
    dir_name = os.path.dirname(os.path.abspath(file))
    if not os.path.isdir(dir_name):
        exit_with_error("directory %s doesn't exist" % dirname)
    if not os.access(dir_name, os.W_OK):
        exit_with_error("file %s may not be writeable" % file)
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
        nargs='+',
        action=FileAction,
        type=str,
        help='source file to be translated/verified')

    parser.add_argument('--version', action='version',
                        version='SMACK version ' + VERSION)

    noise_group = parser.add_mutually_exclusive_group()

    noise_group.add_argument(
        '-q',
        '--quiet',
        action='store_true',
        default=False,
        help='enable quiet output')

    noise_group.add_argument(
        '-v',
        '--verbose',
        action='store_true',
        default=False,
        help='enable verbose output')

    noise_group.add_argument(
        '-d',
        '--debug',
        action="store_true",
        default=False,
        help='enable debugging output')

    noise_group.add_argument(
        '--debug-only',
        metavar='MODULES',
        default=None,
        type=str,
        help='limit debugging output to given MODULES')

    noise_group.add_argument('--warn', default="unsound",
                             choices=['silent', 'unsound', 'info'],
                             help='''enable certain type of warning messages
            (silent: no warning messages;
            unsound: warnings about unsoundness;
            info: warnings about unsoundness and translation information) [default: %(default)s]''')

    parser.add_argument(
        '-t',
        '--no-verify',
        action="store_true",
        default=False,
        help='perform only translation, without verification.')

    parser.add_argument('-w', '--error-file', metavar='FILE', default=None,
                        type=str, help='save error trace/witness to FILE')

    frontend_group = parser.add_argument_group('front-end options')

    frontend_group.add_argument('-x', '--language', metavar='LANG',
                                choices=list(frontends().keys()), default=None,
                                help='Treat input files as having type LANG.')

    frontend_group.add_argument(
        '-bc',
        '--bc-file',
        metavar='FILE',
        default=None,
        action=FileAction,
        type=str,
        help='save initial LLVM bitcode to FILE')

    frontend_group.add_argument(
        '--linked-bc-file',
        metavar='FILE',
        default=None,
        type=str,
        help=argparse.SUPPRESS)

    frontend_group.add_argument(
        '--replay-harness',
        metavar='FILE',
        default='replay-harness.c',
        type=str,
        help=argparse.SUPPRESS)

    frontend_group.add_argument(
        '--replay-exe-file',
        metavar='FILE',
        default='replay-exe',
        type=str,
        help=argparse.SUPPRESS)

    frontend_group.add_argument(
        '-ll',
        '--ll-file',
        metavar='FILE',
        default=None,
        action=FileAction,
        type=str,
        help='save final LLVM IR to FILE')

    frontend_group.add_argument(
        '--clang-options',
        metavar='OPTIONS',
        default='',
        help='additional compiler arguments (e.g., --clang-options="-w -g")')

    translate_group = parser.add_argument_group('translation options')

    translate_group.add_argument(
        '-bpl',
        '--bpl-file',
        metavar='FILE',
        default=None,
        action=FileAction,
        type=str,
        help='save (intermediate) Boogie code to FILE')

    translate_group.add_argument(
        '--no-memory-splitting',
        action="store_true",
        default=False,
        help='disable region-based memory splitting')

    translate_group.add_argument(
        '--mem-mod',
        choices=[
            'no-reuse',
            'no-reuse-impls',
            'reuse'],
        default='no-reuse-impls',
        help='select memory model (no-reuse=never reallocate the same address, reuse=reallocate freed addresses) [default: %(default)s]')

    translate_group.add_argument(
        '--static-unroll',
        action="store_true",
        default=False,
        help='enable static LLVM loop unrolling pass as a preprocessing step')

    translate_group.add_argument(
        '--pthread',
        action='store_true',
        default=False,
        help='enable support for pthread programs')

    translate_group.add_argument(
        '--max-threads',
        default='32',
        type=int,
        help='bound on the number of threads [default: %(default)s]')

    translate_group.add_argument(
        '--bit-precise',
        action="store_true",
        default=False,
        help='model non-pointer values as bit vectors')

    translate_group.add_argument(
        '--timing-annotations',
        action="store_true",
        default=False,
        help='enable timing annotations')

    translate_group.add_argument(
        '--bit-precise-pointers',
        action="store_true",
        default=False,
        help='model pointers and non-pointer values as bit vectors')

    translate_group.add_argument(
        '--no-byte-access-inference',
        action="store_true",
        default=False,
        help='disable bit-precision-related optimizations with DSA')

    translate_group.add_argument(
        '--entry-points',
        metavar='PROC',
        nargs='+',
        default=['main'],
        help='specify top-level procedures [default: %(default)s]')

    translate_group.add_argument(
        '--memory-safety',
        action='store_true',
        default=False,
        help='enable memory safety checks')

    translate_group.add_argument(
        '--only-check-valid-deref',
        action='store_true',
        default=False,
        help='only enable valid dereference checks')

    translate_group.add_argument(
        '--only-check-valid-free',
        action='store_true',
        default=False,
        help='only enable valid free checks')

    translate_group.add_argument(
        '--only-check-memleak',
        action='store_true',
        default=False,
        help='only enable memory leak checks')

    translate_group.add_argument(
        '--integer-overflow',
        action='store_true',
        default=False,
        help='enable integer overflow checks')

    translate_group.add_argument(
        '--llvm-assumes',
        choices=[
            'none',
            'use',
            'check'],
        default='none',
        help='optionally enable generation of Boogie assume statements from LLVM assume statements ' +
        '(none=no generation [default], use=generate assume statements, check=check assume statements)')

    translate_group.add_argument(
        '--float',
        action="store_true",
        default=False,
        help='enable bit-precise floating-point functions')

    translate_group.add_argument(
        '--strings',
        action='store_true',
        default=False,
        help='enable support for string')

    verifier_group = parser.add_argument_group('verifier options')

    verifier_group.add_argument(
        '--verifier',
        choices=[
            'boogie',
            'corral',
            'symbooglix',
            'svcomp'],
        default='corral',
        help='back-end verification engine')

    verifier_group.add_argument('--solver',
                                choices=['z3', 'cvc4', "yices2"], default='z3',
                                help='back-end SMT solver')

    verifier_group.add_argument(
        '--unroll',
        metavar='N',
        default='1',
        type=lambda x: int(x) if int(x) > 0 else parser.error('Unroll bound has to be positive.'),
        help='loop/recursion unroll bound [default: %(default)s]')

    verifier_group.add_argument(
        '--loop-limit',
        metavar='N',
        default='1',
        type=int,
        help='upper bound on minimum loop iterations [default: %(default)s]')

    verifier_group.add_argument(
        '--context-bound',
        metavar='K',
        default='1',
        type=int,
        help='bound on the number of thread contexts in Corral [default: %(default)s]')

    verifier_group.add_argument(
        '--verifier-options',
        metavar='OPTIONS',
        default='',
        help='additional verifier arguments (e.g., --verifier-options="/trackAllVars /staticInlining")')

    verifier_group.add_argument(
        '--time-limit',
        metavar='N',
        default='1200',
        type=int,
        help='verifier time limit, in seconds [default: %(default)s]')

    verifier_group.add_argument(
        '--max-violations',
        metavar='N',
        default='1',
        type=int,
        help='maximum reported assertion violations [default: %(default)s]')

    verifier_group.add_argument('--smackd', action="store_true", default=False,
                                help='generate JSON-format output for SMACKd')

    verifier_group.add_argument(
        '--svcomp-property',
        metavar='FILE',
        default=None,
        type=str,
        help='load SVCOMP property to check from FILE')

    verifier_group.add_argument(
        '--modular',
        action="store_true",
        default=False,
        help='enable contracts-based modular deductive verification (uses Boogie)')

    verifier_group.add_argument(
        '--replay',
        action="store_true",
        default=False,
        help='enable replay of error trace with test harness.')

    plugins_group = parser.add_argument_group('plugins')

    plugins_group.add_argument(
        '--transform-bpl',
        metavar='COMMAND',
        default=None,
        type=str,
        help='transform generated Boogie code via COMMAND')

    plugins_group.add_argument(
        '--transform-out',
        metavar='COMMAND',
        default=None,
        type=str,
        help='transform verifier output via COMMAND')

    args = parser.parse_args()

    if not args.bc_file:
        args.bc_file = temporary_file('a', '.bc', args)

    if not args.linked_bc_file:
        args.linked_bc_file = temporary_file('b', '.bc', args)

    if not args.bpl_file:
        args.bpl_file = 'a.bpl' if args.no_verify else temporary_file(
            'a', '.bpl', args)

    if args.only_check_valid_deref or args.only_check_valid_free or args.only_check_memleak:
        args.memory_safety = True

    if args.bit_precise_pointers:
        args.bit_precise = True

    # TODO are we (still) using this?
    # with open(args.input_file, 'r') as f:
    #   for line in f.readlines():
    #     m = re.match('.*SMACK-OPTIONS:[ ]+(.*)$', line)
    #     if m:
    #       return args = parser.parse_args(m.group(1).split() + sys.argv[1:])

    return args


def target_selection(args):
    """Determine the target architecture based on flags and source files."""
    # TODO more possible clang flags that determine the target?
    if not re.search('-target', args.clang_options):
        src = args.input_files[0]
        if os.path.splitext(src)[1] == '.bc':
            ll = temporary_file(
                os.path.splitext(
                    os.path.basename(src))[0],
                '.ll',
                args)
            try_command(['llvm-dis', '-o', ll, src])
            src = ll
        if os.path.splitext(src)[1] == '.ll':
            with open(src, 'r') as f:
                for line in f:
                    triple = re.findall('^target triple = "(.*)"', line)
                    if len(triple) > 0:
                        args.clang_options += (" -target %s" % triple[0])
                        break


def frontend(args):
    """Generate the LLVM bitcode file."""
    bitcodes = []
    libs = set()
    noreturning_frontend = False

    def add_libs(lang):
        if lang in extra_libs():
            libs.add(extra_libs()[lang])

    if args.language:
        lang = languages()[args.language]
        if lang in ['boogie', 'svcomp', 'json']:
            noreturning_frontend = True

        add_libs(lang)
        frontend = frontends()[lang]
        for input_file in args.input_files:
            bitcode = frontend(input_file, args)
            if bitcode is not None:
                bitcodes.append(bitcode)

    else:
        for input_file in args.input_files:
            lang = languages()[os.path.splitext(input_file)[1][1:]]
            if lang in ['boogie', 'svcomp', 'json']:
                noreturning_frontend = True

            add_libs(lang)
            bitcode = frontends()[lang](input_file, args)
            if bitcode is not None:
                bitcodes.append(bitcode)

    if not noreturning_frontend:
        return link_bc_files(bitcodes, libs, args)


def llvm_to_bpl(args):
    """Translate the LLVM bitcode file to a Boogie source file."""

    cmd = ['llvm2bpl', args.linked_bc_file, '-bpl', args.bpl_file]
    cmd += ['-warn-type', args.warn]
    cmd += ['-sea-dsa=ci']
    # This flag can lead to unsoundness in Rust regressions.
    #cmd += ['-sea-dsa-type-aware']
    if sys.stdout.isatty():
        cmd += ['-colored-warnings']
    cmd += ['-source-loc-syms']
    for ep in args.entry_points:
        cmd += ['-entry-points', ep]
    if args.debug:
        cmd += ['-debug']
    if args.debug_only:
        cmd += ['-debug-only', args.debug_only]
    if args.ll_file:
        cmd += ['-ll', args.ll_file]
    if "impls" in args.mem_mod:
        cmd += ['-mem-mod-impls']
    if args.static_unroll:
        cmd += ['-static-unroll']
    if args.bit_precise:
        cmd += ['-bit-precise']
    if args.timing_annotations:
        cmd += ['-timing-annotations']
    if args.bit_precise_pointers:
        cmd += ['-bit-precise-pointers']
    if args.no_byte_access_inference:
        cmd += ['-no-byte-access-inference']
    if args.no_memory_splitting:
        cmd += ['-no-memory-splitting']
    if args.memory_safety:
        cmd += ['-memory-safety']
    if args.integer_overflow:
        cmd += ['-integer-overflow']
    if args.llvm_assumes:
        cmd += ['-llvm-assumes=' + args.llvm_assumes]
    if args.float:
        cmd += ['-float']
    if args.modular:
        cmd += ['-modular']
    try_command(cmd, console=True)
    annotate_bpl(args)
    property_selection(args)
    transform_bpl(args)


def procedure_annotation(name, args):
    if name in args.entry_points:
        return "{:entrypoint}"
    elif args.modular and re.match("|".join(inlined_procedures()).replace("$", r"\$"), name):
        return "{:inline 1}"
    elif (not args.modular) and args.verifier == 'boogie':
        return ("{:inline %s}" % args.unroll)
    else:
        return ""


def annotate_bpl(args):
    """Annotate the Boogie source file with additional metadata."""

    proc_decl = re.compile(r'procedure\s+([^\s(]*)\s*\(')

    with open(args.bpl_file, 'r+') as f:
        bpl = "// generated by SMACK version %s for %s\n" % (
            VERSION, args.verifier)
        bpl += "// via %s\n\n" % " ".join(sys.argv)
        bpl += proc_decl.sub(lambda m: ("procedure %s %s(" %
                                        (procedure_annotation(m.group(1), args), m.group(1))), f.read())
        f.seek(0)
        f.truncate()
        f.write(bpl)


def property_selection(args):
    selected_props = []
    if args.only_check_valid_deref:
        selected_props.append('valid_deref')
    elif args.only_check_valid_free:
        selected_props.append('valid_free')
    elif args.only_check_memleak:
        selected_props.append('valid_memtrack')

    def replace_assertion(m):
        if len(selected_props) > 0:
            if m.group(2) and m.group(3) in selected_props:
                attrib = m.group(2)
                expr = m.group(4)
            else:
                attrib = ''
                expr = 'true'
            return m.group(1) + attrib + expr + ";"
        else:
            return m.group(0)

    with open(args.bpl_file, 'r+') as f:
        lines = f.readlines()
        f.seek(0)
        f.truncate()
        for line in lines:
            line = re.sub(
                r'^(\s*assert\s*)({:(.+)})?(.+);',
                replace_assertion,
                line)
            f.write(line)


def transform_bpl(args):
    if args.transform_bpl:
        with open(args.bpl_file, 'r+') as bpl:
            old = bpl.read()
            bpl.seek(0)
            bpl.truncate()
            tx = subprocess.Popen(
                shlex.split(
                    args.transform_bpl),
                stdin=subprocess.PIPE,
                stdout=bpl,
                universal_newlines=True)
            tx.communicate(input=old)


def transform_out(args, old):
    out = old
    if args.transform_out:
        tx = subprocess.Popen(shlex.split(args.transform_out),
                              stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                              stderr=subprocess.PIPE, universal_newlines=True)
        out, err = tx.communicate(input=old)
    return out


def verification_result(verifier_output):
    if re.search(
        r'[1-9]\d* time out|Z3 ran out of resources|timed out|ERRORS_TIMEOUT',
            verifier_output):
        return 'timeout'
    elif re.search(r'[1-9]\d* verified, 0 errors?|no bugs|NO_ERRORS_NO_TIMEOUT', verifier_output):
        return 'verified'
    elif re.search(r'\d* verified, [1-9]\d* errors?|can fail|ERRORS_NO_TIMEOUT', verifier_output):
        if re.search(
            r'ASSERTION FAILS assert {:valid_deref}',
                verifier_output):
            return 'invalid-deref'
        elif re.search(r'ASSERTION FAILS assert {:valid_free}', verifier_output):
            return 'invalid-free'
        elif re.search(r'ASSERTION FAILS assert {:valid_memtrack}', verifier_output):
            return 'invalid-memtrack'
        elif re.search(r'ASSERTION FAILS assert {:overflow}', verifier_output):
            return 'overflow'
        else:
            listCall = re.findall(r'\(CALL .+\)', verifier_output)
            if len(listCall) > 0 and re.search(
                    r'free_', listCall[len(listCall) - 1]):
                return 'invalid-free'
            else:
                return 'error'
    else:
        return 'unknown'


def verify_bpl(args):
    """Verify the Boogie source file with a back-end verifier."""

    if args.verifier == 'svcomp':
        verify_bpl_svcomp(args)
        return

    elif args.verifier == 'boogie' or args.modular:
        command = ["boogie"]
        command += [args.bpl_file]
        command += ["/nologo", "/doModSetAnalysis"]
        command += ["/useArrayTheory"]
        command += ["/timeLimit:%s" % args.time_limit]
        command += ["/errorLimit:%s" % args.max_violations]
        command += ["/proverOpt:O:smt.array.extensional=false"]
        command += ["/proverOpt:O:smt.qi.eager_threshold=100"]
        if not args.modular:
            command += ["/loopUnroll:%d" % args.unroll]
        if args.solver == 'cvc4':
            command += ["/proverOpt:SOLVER=cvc4"]
        elif args.solver == 'yices2':
            command += ["/proverOpt:SOLVER=Yices2"]

    elif args.verifier == 'corral':
        command = ["corral"]
        command += [args.bpl_file]
        command += ["/tryCTrace", "/noTraceOnDisk", "/printDataValues:1"]
        command += ["/k:%d" % args.context_bound]
        command += ["/useProverEvaluate"]
        command += ["/timeLimit:%s" % args.time_limit]
        command += ["/cex:%s" % args.max_violations]
        command += ["/maxStaticLoopBound:%d" % args.loop_limit]
        command += ["/recursionBound:%d" % args.unroll]
        command += ["/bopt:proverOpt:O:smt.qi.eager_threshold=100"]
        if args.solver == 'cvc4':
            command += ["/bopt:proverOpt:SOLVER=cvc4"]
        elif args.solver == 'yices2':
            command += ["/bopt:proverOpt:SOLVER=Yices2"]

    elif args.verifier == 'symbooglix':
        command = ['symbooglix']
        command += [args.bpl_file]
        command += ["--file-logging=0"]
        command += ["--entry-points=%s" % ",".join(args.entry_points)]
        command += ["--timeout=%d" % args.time_limit]
        command += ["--max-loop-depth=%d" % args.unroll]

    if args.verifier_options:
        command += args.verifier_options.split()

    verifier_output = try_command(command, timeout=args.time_limit)
    verifier_output = transform_out(args, verifier_output)
    result = verification_result(verifier_output)

    if args.smackd:
        print(smackdOutput(verifier_output))

    elif result == 'verified':
        print(results(args)[result])

    else:
        if result == 'error' or result == 'invalid-deref' or result == 'invalid-free' or result == 'invalid-memtrack' or result == 'overflow':
            error = error_trace(verifier_output, args)

            if args.error_file:
                with open(args.error_file, 'w') as f:
                    f.write(error)

            if not args.quiet:
                print(error)

            if args.replay:
                replay_error_trace(verifier_output, args)

        sys.exit(results(args)[result])


def error_step(step):
    FILENAME = r'[\w#$~%.\/-]*'
    step = re.match(r"(\s*)(%s)\((\d+),\d+\): (.*)" % FILENAME, step)
    if step:
        if re.match('.*[.]bpl$', step.group(2)):
            line_no = int(step.group(3))
            message = step.group(4)
            if re.match(r'.*\$bb\d+.*', message):
                message = ""
            with open(step.group(2)) as f:
                for line in f.read().splitlines(True)[line_no:line_no + 10]:
                    src = re.match(
                        r".*{:sourceloc \"(%s)\", (\d+), (\d+)}" %
                        FILENAME, line)
                    if src:
                        return "%s%s(%s,%s): %s" % (step.group(1), src.group(
                            1), src.group(2), src.group(3), message)
        else:
            return corral_error_step(step.group(0))
    else:
        return None


def reformat_assignment(line):
    def repl(m):
        val = m.group(1)
        if 'bv' in val:
            return m.group(2) + 'UL'
        else:
            sig_size = int(m.group(7))
            exp_size = int(m.group(8))
            # assume we can only handle double
            if sig_size > 53 or exp_size > 11:
                return m.group()

            sign_val = -1 if m.group(3) != '' else 1
            sig_val = m.group(4)
            exp_sign_val = -1 if m.group(5) != '' else 1
            # note that the exponent base is 16
            exp_val = 2**(4 * exp_sign_val * int(m.group(6)))
            return str(sign_val * float.fromhex(sig_val) * exp_val)

    # Boogie FP const grammar: (-)0x[sig]e[exp]f[sigSize]e[expSize], where
    # sig = hexdigit {hexdigit} '.' hexdigit {hexdigit}
    # exp = digit {digit}
    # sigSize = digit {digit}
    # expSize = digit {digit}
    return re.sub(
        r'((\d+)bv\d+|(-?)0x([0-9a-fA-F]+\.[0-9a-fA-F]+)e(-?)(\d+)f(\d+)e(\d+))',
        repl,
        line.strip())


def demangle(func):
    def demangle_with(func, tool):
        if shutil.which(tool):
            p = subprocess.Popen(
                tool,
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE)
            out, _ = p.communicate(input=func.encode())
            return out.decode()
        return func
    return functools.reduce(demangle_with, ['cxxfilt', 'rustfilt'], func)


def transform(info):
    info = info.strip()
    if info.startswith('CALL') or info.startswith('RETURN from'):
        tokens = info.split()
        tokens[-1] = demangle(tokens[-1])
        return ' '.join(tokens)
    elif '=' in info:
        tokens = info.split('=')
        lhs = tokens[0].strip()
        rhs = tokens[1].strip()
        return demangle(lhs) + ' = ' + reformat_assignment(rhs)
    else:
        return info


def corral_error_step(step):
    m = re.match(r'([^\s]*)\s+Trace:\s+(Thread=\d+)\s+\((.*)[\)|;]', step)
    if m:
        path = m.group(1)
        tid = m.group(2)
        info = ','.join(map(transform, [x for x in m.group(3).split(',') if not re.search(
            '((CALL|RETURN from)\s+(\$|__SMACK))|Done|ASSERTION', x)]))
        return '{0}\t{1}  {2}'.format(path, tid, info)
    else:
        return step


def error_trace(verifier_output, args):
    trace = ""
    for line in verifier_output.splitlines(True):
        step = error_step(line)
        if step:
            m = re.match('(.*): [Ee]rror [A-Z0-9]+: (.*)', step)
            if m:
                trace += "%s: %s\nExecution trace:\n" % (
                    m.group(1), m.group(2))
            else:
                trace += ('' if step[0] == ' ' else '    ') + step + "\n"

    return trace


def smackdOutput(corralOutput):
    FILENAME = r'[\w#$~%.\/-]+'
    traceP = re.compile(
        '(' + FILENAME + r')\((\d+),(\d+)\): Trace: Thread=(\d+)  (\((.*)[\);])?$')
    errorP = re.compile('(' + FILENAME + r')\((\d+),(\d+)\): (error .*)$')

    passedMatch = re.search('Program has no bugs', corralOutput)
    if passedMatch:
        json_data = {
            'verifier': 'corral',
            'passed?': True
        }

    else:
        traces = []
        filename = ''
        lineno = 0
        colno = 0
        threadid = 0
        desc = ''
        for traceLine in corralOutput.splitlines(True):
            traceMatch = traceP.match(traceLine)
            if traceMatch:
                filename = str(traceMatch.group(1))
                lineno = int(traceMatch.group(2))
                colno = int(traceMatch.group(3))
                threadid = int(traceMatch.group(4))
                desc = str(traceMatch.group(6))
                for e in desc.split(','):
                    e = e.strip()
                    assm = re.sub(
                        r'=(\s*\d+)bv\d+',
                        r'=\1',
                        e) if '=' in e else ''
                    trace = {'threadid': threadid,
                             'file': filename,
                             'line': lineno,
                             'column': colno,
                             'description': e,
                             'assumption': assm}
                    traces.append(trace)
            else:
                errorMatch = errorP.match(traceLine)
                if errorMatch:
                    filename = str(errorMatch.group(1))
                    lineno = int(errorMatch.group(2))
                    colno = int(errorMatch.group(3))
                    desc = str(errorMatch.group(4))

        failsAt = {
            'file': filename,
            'line': lineno,
            'column': colno,
            'description': desc}

        json_data = {
            'verifier': 'corral',
            'passed?': False,
            'failsAt': failsAt,
            'threadCount': 1,
            'traces': traces
        }
    json_string = json.dumps(json_data)
    return json_string


def clean_up_upon_sigterm(main):
    def handler(signum, frame):
        remove_temp_files()
        sys.exit(0)
    signal.signal(signal.SIGTERM, handler)
    return main


@clean_up_upon_sigterm
def main():
    try:
        global args
        args = arguments()

        target_selection(args)

        if not args.quiet:
            print("SMACK program verifier version %s" % VERSION)

        frontend(args)

        if args.no_verify:
            if not args.quiet:
                print("SMACK generated %s" % args.bpl_file)
        else:
            verify_bpl(args)

    except KeyboardInterrupt:
        sys.exit("SMACK aborted by keyboard interrupt.")

    finally:
        remove_temp_files()
